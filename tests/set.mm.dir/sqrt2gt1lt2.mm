include "c1.mm"
include "c2.mm"
include "csqrt.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "sqrt1.mm"
include "1lt2.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wb.mm"
include "1re.mm"
include "0le1.mm"
include "2re.mm"
include "0le2.mm"
include "sqrtlt.mm"
include "mp4an.mm"
include "mpbi.mm"
include "eqbrtrri.mm"
include "c4.mm"
include "2lt4.mm"
include "4re.mm"
include "0re.mm"
include "4pos.mm"
include "ltleii.mm"
include "sqrt4.mm"
include "breqtri.mm"
include "pm3.2i.mm"

theorem sqrt2gt1lt2



  assert |- ( 1 < ( sqrt ` 2 ) /\ ( sqrt ` 2 ) < 2 )

  proof
    c1
    c2
    csqrt
    cfv
    #
    clt
    wbr
    @0
    c2
    clt
    wbr
    c1
    csqrt
    cfv
    #
    c1
    @0
    clt
    sqrt1
    c1
    c2
    clt
    wbr
    #
    @1
    @0
    clt
    wbr
    #
    1lt2
    c1
    cr
    wcel
    cc0
    c1
    cle
    wbr
    c2
    cr
    wcel
    #
    cc0
    c2
    cle
    wbr
    #
    @2
    @3
    wb
    1re
    0le1
    2re
    0le2
    c1
    c2
    sqrtlt
    mp4an
    mpbi
    eqbrtrri
    @0
    c4
    csqrt
    cfv
    #
    c2
    clt
    c2
    c4
    clt
    wbr
    #
    @0
    @6
    clt
    wbr
    #
    2lt4
    @4
    @5
    c4
    cr
    wcel
    cc0
    c4
    cle
    wbr
    @7
    @8
    wb
    2re
    0le2
    4re
    cc0
    c4
    0re
    4re
    4pos
    ltleii
    c2
    c4
    sqrtlt
    mp4an
    mpbi
    sqrt4
    breqtri
    pm3.2i
end
