include "cr.mm"
include "wcel.mm"
include "cchp.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "c2.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "cle.mm"
include "wne.mm"
include "wb.mm"
include "2re.mm"
include "lenlt.mm"
include "mpan.mm"
include "wa.mm"
include "chprpcl.mm"
include "rpne0d.mm"
include "ex.mm"
include "sylbird.mm"
include "necon4bd.mm"
include "cfl.mm"
include "c1.mm"
include "reflcl.mm"
include "adantr.mm"
include "1red.mm"
include "caddc.mm"
include "co.mm"
include "cz.mm"
include "2z.mm"
include "fllt.mm"
include "mpan2.mm"
include "biimpa.mm"
include "df-2.mm"
include "syl6breq.mm"
include "flcl.mm"
include "1z.mm"
include "zleltp1.mm"
include "sylancl.mm"
include "mpbird.mm"
include "chpwordi.mm"
include "syl3anc.mm"
include "chpfl.mm"
include "chp1.mm"
include "a1i.mm"
include "3brtr3d.mm"
include "chpge0.mm"
include "chpcl.mm"
include "0re.mm"
include "letri3.mm"
include "mpbir2and.mm"
include "impbid.mm"

theorem chpeq0
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vx: setvar x
  let cN: class N


  assert |- ( A e. RR -> ( ( psi ` A ) = 0 <-> A < 2 ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cchp
    cfv
    #
    cc0
    wceq
    #
    cA
    c2
    clt
    wbr
    #
    @0
    @3
    @1
    cc0
    @0
    @3
    wn
    #
    c2
    cA
    cle
    wbr
    #
    @1
    cc0
    wne
    #
    c2
    cr
    wcel
    @0
    @5
    @4
    wb
    2re
    c2
    cA
    lenlt
    mpan
    @0
    @5
    @6
    @0
    @5
    wa
    @1
    cA
    chprpcl
    rpne0d
    ex
    sylbird
    necon4bd
    @0
    @3
    @2
    @0
    @3
    wa
    #
    @2
    @1
    cc0
    cle
    wbr
    #
    cc0
    @1
    cle
    wbr
    #
    @7
    cA
    cfl
    cfv
    #
    cchp
    cfv
    #
    c1
    cchp
    cfv
    #
    @1
    cc0
    cle
    @7
    @10
    cr
    wcel
    #
    c1
    cr
    wcel
    @10
    c1
    cle
    wbr
    #
    @11
    @12
    cle
    wbr
    @0
    @13
    @3
    cA
    reflcl
    adantr
    @7
    1red
    @7
    @14
    @10
    c1
    c1
    caddc
    co
    #
    clt
    wbr
    #
    @7
    @10
    c2
    @15
    clt
    @0
    @3
    @10
    c2
    clt
    wbr
    #
    @0
    c2
    cz
    wcel
    @3
    @17
    wb
    2z
    cA
    c2
    fllt
    mpan2
    biimpa
    df-2
    syl6breq
    @7
    @10
    cz
    wcel
    #
    c1
    cz
    wcel
    @14
    @16
    wb
    @0
    @18
    @3
    cA
    flcl
    adantr
    1z
    @10
    c1
    zleltp1
    sylancl
    mpbird
    @10
    c1
    chpwordi
    syl3anc
    @0
    @11
    @1
    wceq
    @3
    cA
    chpfl
    adantr
    @12
    cc0
    wceq
    @7
    chp1
    a1i
    3brtr3d
    @0
    @9
    @3
    cA
    chpge0
    adantr
    @7
    @1
    cr
    wcel
    #
    cc0
    cr
    wcel
    @2
    @8
    @9
    wa
    wb
    @0
    @19
    @3
    cA
    chpcl
    adantr
    0re
    @1
    cc0
    letri3
    sylancl
    mpbir2and
    ex
    impbid
end
