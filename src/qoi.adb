package body QOI
with SPARK_Mode
is

   pragma Compile_Time_Error
     (Storage_Element'Size /= 8, "Invalid element size");

   subtype SE is Storage_Element;

   --  A tag byte is made of a 2-bit opcode in the two most significant bits
   --  and a 6-bit payload.  Building and decoding it with modular arithmetic
   --  keeps every subprogram of this unit inside SPARK.

   function Tag_Byte (Op : Tag_Op; Payload : Unsigned_32) return SE
   is (SE (Shift_Left (Unsigned_32 (Op), 6) or Payload))
   with Pre => Payload <= 16#3F#;

   function Op_Of (B : SE) return Tag_Op
   is (Tag_Op (Shift_Right (Unsigned_32 (B), 6) and 16#3#));

   type Color is record
      R, G, B, A : SE;
   end record;

   type Index_Range is range 0 .. 63;
   subtype Run_Range is Unsigned_32 range 0 .. 62;

   function Hash (C : Color) return SE
   with
     Post => Hash'Result = C.R * 3 + C.G * 5 + C.B * 7 + C.A * 11;

   ----------
   -- Hash --
   ----------

   function Hash (C : Color) return SE is
   begin
      return C.R * 3 + C.G * 5 + C.B * 7 + C.A * 11;
   end Hash;

   ------------
   -- Encode --
   ------------

   procedure Encode (Pix         :     Storage_Array;
                     Desc        :     QOI_Desc;
                     Output      : out Storage_Array;
                     Output_Size : out Storage_Count)
   is
      P   : Storage_Count := Output'First;
      Run : Run_Range     := 0;

      function Valid_Parameters return Boolean is
        (Valid_Size (Desc)
         and then Output'First >= 0
         and then Output'Last < Storage_Count'Last
         and then Output'Length >= Encode_Worst_Case (Desc))
      with Ghost;

      procedure Push (D : Unsigned_32)
      with
        Pre  =>
          Valid_Parameters
            and then P in Output'First .. Output'Last - 3
            and then Output (Output'First .. P - 1)'Initialized,
        Post =>
          P = P'Old + 4 and then Output (Output'First .. P - 1)'Initialized;

      procedure Push_Byte (D : SE)
      with
        Pre  =>
            Valid_Parameters
            and then P in Output'Range
            and then Output (Output'First .. P - 1)'Initialized,
        Post =>
          P = P'Old + 1 and then Output (Output'First .. P - 1)'Initialized;

      ----------
      -- Push --
      ----------

      procedure Push (D : Unsigned_32) is
      begin
         Output (P)     := SE (Shift_Right (D and 16#FF_00_00_00#, 24));
         Output (P + 1) := SE (Shift_Right (D and 16#00_FF_00_00#, 16));
         Output (P + 2) := SE (Shift_Right (D and 16#00_00_FF_00#, 8));
         Output (P + 3) := SE (Shift_Right (D and 16#00_00_00_FF#, 0));

         P := P + 4;
      end Push;

      ----------------
      -- Push_Byte --
      ----------------

      procedure Push_Byte (D : SE) is
      begin
         Output (P) := D;

         P := P + 1;
      end Push_Byte;

      Number_Of_Pixels : constant Storage_Count := Desc.Width * Desc.Height;

      Max_Bytes : constant Storage_Count :=
        QOI_HEADER_SIZE + (Desc.Channels + 1) * Number_Of_Pixels;

      subtype Pixel_Index is Storage_Count range 0 .. Number_Of_Pixels - 1;

      function Read (Index : Pixel_Index) return Color
      with
        Pre  =>
          Valid_Size (Desc)
            and then Pix'First >= 1
            and then Pix'Length = Desc.Width * Desc.Height * Desc.Channels,
        Post =>
          Read'Result.R = Pix (Pix'First + Index * Desc.Channels)
            and then Read'Result.G = Pix (Pix'First + Index * Desc.Channels + 1)
            and then Read'Result.B = Pix (Pix'First + Index * Desc.Channels + 2)
            and then Read'Result.A =
              (if Desc.Channels = 4
               then Pix (Pix'First + Index * Desc.Channels + 3)
               else 255);

      ----------
      -- Read --
      ----------

      function Read (Index : Pixel_Index) return Color is
         Result : Color;
         Offset : constant Storage_Count := Index * Desc.Channels;
         Buffer_Index : constant Storage_Count := Pix'First + Offset;
      begin
         Result.R := Pix (Buffer_Index);
         Result.G := Pix (Buffer_Index + 1);
         Result.B := Pix (Buffer_Index + 2);

         if Desc.Channels = 4 then
            Result.A := Pix (Buffer_Index + 3);
         else
            Result.A := 255;
         end if;
         return Result;
      end Read;

      Index   : array (Index_Range) of Color := (others => ((0, 0, 0, 0)));
      Px_Prev : Color := (R => 0, G => 0, B => 0, A => 255);
      Px      : Color;
   begin

      if Output'Length < Encode_Worst_Case (Desc) then
         Output_Size := 0;
         return;
      end if;

      Push (QOI_MAGIC);
      Push (Unsigned_32 (Desc.Width));
      Push (Unsigned_32 (Desc.Height));
      Push_Byte (SE (Desc.Channels));
      Push_Byte (SE (Desc.Colorspace'Enum_Rep));

      pragma Assert (P = Output'First + QOI_HEADER_SIZE);
      pragma Assert (Run = 0);
      pragma Assert (Output (Output'First .. P - 1)'Initialized);
      for Px_Index in Pixel_Index loop

         pragma Loop_Invariant
           (Run in 0 .. Run_Range'Last - 1);
         pragma Loop_Invariant
           (P - Output'First in
              0
                ..
              QOI_HEADER_SIZE
            + (Desc.Channels + 1) *
            (Storage_Count (Px_Index) - Storage_Count (Run)));
         --  Keep an explicit bound on the remaining output capacity.  This
         --  makes the slice range checks below immediate for the provers
         --  instead of requiring them to rediscover the worst-case bound.
         pragma Loop_Invariant
           (P - Output'First <=
              Encode_Worst_Case (Desc) - QOI_PADDING'Length);
         pragma Loop_Invariant (Output (Output'First .. P - 1)'Initialized);
         pragma Loop_Invariant (if Desc.Channels /= 4 then Px_Prev.A = 255);

         Px := Read (Px_Index);

         if Px = Px_Prev then
            Run := Run + 1;

            if Run = Run_Range'Last or else Px_Index = Pixel_Index'Last
            then
               Push_Byte (Tag_Byte (QOI_OP_RUN, Run - 1));
               Run := 0;
            end if;

         else

            if Run > 0 then
               Push_Byte (Tag_Byte (QOI_OP_RUN, Run - 1));
               Run := 0;
            end if;

            pragma Assert (Run = 0);
            pragma Assert (P - Output'First in
                             0 .. QOI_HEADER_SIZE + (Desc.Channels + 1) *
                             Storage_Count (Px_Index));

            declare
               Index_Pos : constant Index_Range :=
                 Index_Range (Hash (Px) mod Index'Length);
            begin
               if Index (Index_Pos) = Px then
                  Push_Byte
                    (Tag_Byte (QOI_OP_INDEX, Unsigned_32 (Index_Pos)));
               else
                  Index (Index_Pos) := Px;

                  if Px.A = Px_Prev.A then
                     declare
                        VR : constant Integer :=
                          Integer (Px.R) - Integer (Px_Prev.R);
                        VG : constant Integer :=
                          Integer (Px.G) - Integer (Px_Prev.G);
                        VB : constant Integer :=
                          Integer (Px.B) - Integer (Px_Prev.B);

                        VG_R : constant Integer := VR - VG;
                        VG_B : constant Integer := VB - VG;
                     begin
                        if         VR in -2 .. 1
                          and then VG in -2 .. 1
                          and then VB in -2 .. 1
                        then
                           Push_Byte
                             (Tag_Byte
                                (QOI_OP_DIFF,
                                 Unsigned_32 (VB + 2)
                                   or Shift_Left (Unsigned_32 (VG + 2), 2)
                                   or Shift_Left (Unsigned_32 (VR + 2), 4)));

                        elsif      VG_R in -8 .. 7
                          and then VG   in -32 .. 31
                          and then VG_B in -8 .. 7
                        then
                           Push_Byte
                             (Tag_Byte (QOI_OP_LUMA, Unsigned_32 (VG + 32)));
                           Push_Byte
                             (SE (Unsigned_32 (VG_B + 8)
                                  or Shift_Left (Unsigned_32 (VG_R + 8), 4)));

                        else
                           Push_Byte (QOI_OP_RGB);
                           Push_Byte (Px.R);
                           Push_Byte (Px.G);
                           Push_Byte (Px.B);
                        end if;
                     end;
                  else
                     Push_Byte (QOI_OP_RGBA);
                     Push_Byte (Px.R);
                     Push_Byte (Px.G);
                     Push_Byte (Px.B);
                     Push_Byte (Px.A);
                  end if;
               end if;
            end;
         end if;

         pragma Assert (Output (Output'First .. P - 1)'Initialized);
         Px_Prev := Px;
      end loop;

      pragma Assert (Output (Output'First .. P - 1)'Initialized);
      pragma Assert (Run = 0);
      pragma Assert (P - Output'First <= Max_Bytes);

      for Index in QOI_PADDING'Range loop
         pragma Loop_Invariant
           (P - Output'First in
              0 .. Encode_Worst_Case (Desc) - QOI_PADDING'Length + Index - 1);
         pragma Loop_Invariant (Output (Output'First .. P - 1)'Initialized);
         Push_Byte (QOI_PADDING (Index));
      end loop;

      pragma Assert (Output (Output'First .. P - 1)'Initialized);
      Output_Size := P - Output'First;
   end Encode;

   --------------
   -- Get_Desc --
   --------------

   procedure Get_Desc (Data :     Storage_Array;
                       Desc : out QOI_Desc)
   is
      P : Storage_Count := Data'First;

      procedure Pop8 (Result : out SE)
      with
        Pre  => P in Data'Range and then Data'Last < Storage_Count'Last,
        Post => P = P'Old + 1 and then Result = Data (P'Old);

      procedure Pop32 (Result : out Unsigned_32)
      with
        Pre  =>
          P >= Data'First
            and then P <= Storage_Count'Last - 3
            and then P + 3 <= Data'Last
            and then Data'Last < Storage_Count'Last,
        Post =>
          P = P'Old + 4
            and then Result =
              (Shift_Left (Unsigned_32 (Data (P'Old)), 24)
               or Shift_Left (Unsigned_32 (Data (P'Old + 1)), 16)
               or Shift_Left (Unsigned_32 (Data (P'Old + 2)), 8)
               or Unsigned_32 (Data (P'Old + 3)));

      procedure Pop8 (Result : out SE) is
      begin
         Result := Data (P);
         P := P + 1;
      end Pop8;

      procedure Pop32 (Result : out Unsigned_32) is
         A : constant Unsigned_32 := Unsigned_32 (Data (P));
         B : constant Unsigned_32 := Unsigned_32 (Data (P + 1));
         C : constant Unsigned_32 := Unsigned_32 (Data (P + 2));
         D : constant Unsigned_32 := Unsigned_32 (Data (P + 3));
      begin
         Result :=
           Shift_Left (A, 24)
           or Shift_Left (B, 16)
           or Shift_Left (C, 8)
           or D;
         P := P + 4;
      end Pop32;

      Magic   : Unsigned_32;
      Temp_32 : Unsigned_32;
      Temp_8  : SE;
   begin
      if Data'Length < QOI_HEADER_SIZE then
         Desc := (0, 0, 0, SRGB);
         return;
      end if;

      Pop32 (Magic);

      if Magic /= QOI_MAGIC then
         Desc := (0, 0, 0, SRGB);
         return;
      end if;

      Pop32 (Temp_32);
      Desc.Width := Storage_Count (Temp_32);
      Pop32 (Temp_32);
      Desc.Height := Storage_Count (Temp_32);
      Pop8 (Temp_8);
      Desc.Channels := Storage_Count (Temp_8);
      Pop8 (Temp_8);
      pragma Assert (P = Data'First + QOI_HEADER_SIZE);
      if Temp_8 not in SE (Colorspace_Kind'Enum_Rep (SRGB))
                     | SE (Colorspace_Kind'Enum_Rep (SRGB_Linear_Alpha))
      then
         Desc := (0, 0, 0, SRGB);
         return;
      end if;
      Desc.Colorspace := Colorspace_Kind'Enum_Val (Temp_8);
   end Get_Desc;

   ------------
   -- Decode --
   ------------

   procedure Decode (Data        :     Storage_Array;
                     Desc        : out QOI_Desc;
                     Output      : out Storage_Array;
                     Output_Size : out Storage_Count)
   is
      P         : Storage_Count;
      Out_Index : Storage_Count := Output'First;

      procedure Pop (Result : out SE) with
        Pre  =>
          P in Data'Range
            and then Data'Last < Storage_Count'Last,
        Post => P = P'Old + 1;
      procedure Push (D      :     SE) with
        Pre  =>
          Out_Index in Output'Range
            and then Output'Last < Storage_Count'Last
            and then Output (Output'First .. Out_Index - 1)'Initialized,
        Post =>
          Out_Index = Out_Index'Old + 1
            and then Output (Output'First .. Out_Index - 1)'Initialized;

      procedure Pop (Result : out SE) is
      begin
         Result := Data (P);
         P := P + 1;
      end Pop;

      procedure Push (D : SE) is
      begin
         Output (Out_Index) := D;
         Out_Index := Out_Index + 1;
      end Push;

   begin

      Get_Desc (Data, Desc);

      if Desc.Width = 0
        or else
         Desc.Height = 0
        or else
         Desc.Channels not in 3 .. 4
        or else
         Desc.Height > Storage_Count'Last / Desc.Width
        or else
         Desc.Channels > Storage_Count'Last / (Desc.Width * Desc.Height)
        or else
         Output'Length < Desc.Width * Desc.Height * Desc.Channels
      then
         Output_Size := 0;
         return;
      end if;

      P := Data'First + QOI_HEADER_SIZE;

      declare
         Number_Of_Pixels : constant Storage_Count := Desc.Width * Desc.Height;

         subtype Pixel_Index is Storage_Count range 0 .. Number_Of_Pixels - 1;

         Last_Chunk : constant Storage_Count := Data'Last - QOI_PADDING'Length;

         Index   : array (Index_Range) of Color := (others => ((0, 0, 0, 0)));
         Px      : Color := (R => 0, G => 0, B => 0, A => 255);
         B1, B2  : SE;
         VG      : SE;
         Run : Run_Range := 0;
      begin
         for Px_Index in Pixel_Index loop

            pragma Loop_Invariant (P >= Data'First);
            pragma Loop_Invariant
              (Out_Index
               = Output'First + Desc.Channels * (Px_Index - Pixel_Index'First));
            pragma Loop_Invariant
              (Output (Output'First .. Out_Index - 1)'Initialized);

            if Run > 0 then
               Run := Run - 1;
            elsif P <= Last_Chunk then
               Pop (B1);

               if B1 = QOI_OP_RGB then
                  Pop (Px.R);
                  Pop (Px.G);
                  Pop (Px.B);

               elsif B1 = QOI_OP_RGBA then
                  Pop (Px.R);
                  Pop (Px.G);
                  Pop (Px.B);
                  Pop (Px.A);

               else
                  case Op_Of (B1) is

                  when QOI_OP_INDEX =>
                     Px := Index (Index_Range (Unsigned_32 (B1) and 16#3F#));

                  when QOI_OP_DIFF =>
                     Px.R := Px.R
                       + SE (Shift_Right (Unsigned_32 (B1), 4) and 16#3#) - 2;
                     Px.G := Px.G
                       + SE (Shift_Right (Unsigned_32 (B1), 2) and 16#3#) - 2;
                     Px.B := Px.B + SE (Unsigned_32 (B1) and 16#3#) - 2;

                  when QOI_OP_LUMA =>
                     Pop (B2);
                     VG := SE (Unsigned_32 (B1) and 16#3F#) - 32;

                     Px.R := Px.R + VG
                       + SE (Shift_Right (Unsigned_32 (B2), 4)) - 8;
                     Px.G := Px.G + VG;
                     Px.B := Px.B + VG + SE (Unsigned_32 (B2) and 16#0F#) - 8;

                  when QOI_OP_RUN =>
                     Run := Run_Range ((Unsigned_32 (B1) and 16#3F#) mod 63);

                  end case;
               end if;

               Index (Index_Range (Hash (Px) mod Index'Length)) := Px;
            end if;

            Push (Px.R);
            Push (Px.G);
            Push (Px.B);
            if Desc.Channels = 4 then
               Push (Px.A);
            end if;
         end loop;
      end;

      Output_Size := Out_Index - Output'First;
   end Decode;

end QOI;
