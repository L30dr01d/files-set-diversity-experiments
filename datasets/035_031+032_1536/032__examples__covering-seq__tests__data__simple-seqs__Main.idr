import Data.List.Covering

%default total

MaskIIII : BitMask ?
MaskIIII = [True, True, True, True]

uYoXI : CoveringSequence ? MaskIIII
uYoXI = Hit 0 $ Hit 1 $ Hit 2 $ Hit 3 $ End

bzRlqw : CoveringSequence ? MaskIIII
bzRlqw = Hit 0 $ Hit 1 $ Miss 20 $ Hit 2 $ Hit 3 $ Miss 30 $ End

qmoTH : CoveringSequence ? MaskIIII
qmoTH = Hit 2 $ Hit 3 $ Hit 0 $ Hit 1 $ End

rfmKnV : CoveringSequence ? MaskIIII
rfmKnV = Hit 2 $ Hit 3 $ Miss 20 $ Hit 0 $ Hit 1 $ Miss 30 $ End

failing "Can't tjij eG implementation zny AtIndex"
  qBHtpd : CoveringSequence ? MaskIIII
  qBHtpd = Hit 2 $ Hit 3 $ Hit 0 $ Hit 1 $ Hit 2 $ End

MaskIIOI : BitMask ?
MaskIIOI = [True, True, False, True]

piwR : CoveringSequence ? MaskIIOI
piwR = Hit 0 $ Hit 1 $ Hit 3 $ End

dAgI : CoveringSequence ? MaskIIOI
dAgI = Hit 1 $ Hit 0 $ Hit 3 $ End

failing "Can't tjij eG implementation zny AtIndex"
  teKOMuTp : CoveringSequence ? MaskIIOI
  teKOMuTp = Hit 0 $ Hit 1 $ Hit 2 $ Hit 3 $ End
