include "c1.mm"
include "cneg.mm"
include "wcel.mm"
include "cc0.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "neg1z.mm"
include "1le1.mm"
include "cv.mm"
include "cabs.mm"
include "cfv.mm"
include "wceq.mm"
include "fveq2.mm"
include "ax-1cn.mm"
include "absnegi.mm"
include "abs1.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "breq1d.mm"
include "elrab2.mm"
include "mpbir2an.mm"
include "0z.mm"
include "0le1.mm"
include "abs0.mm"
include "1z.mm"
include "3pm3.2i.mm"

theorem lgslem2
  let vx: setvar x
  let cZ: class Z
  assume lgslem2.z: |- Z = { x e. ZZ | ( abs ` x ) <_ 1 }


  assert |- ( -u 1 e. Z /\ 0 e. Z /\ 1 e. Z )

  proof
    c1
    cneg
    #
    cZ
    wcel
    #
    cc0
    cZ
    wcel
    #
    c1
    cZ
    wcel
    #
    @1
    @0
    cz
    wcel
    c1
    c1
    cle
    wbr
    #
    neg1z
    1le1
    vx
    cv
    #
    cabs
    cfv
    #
    c1
    cle
    wbr
    #
    @4
    vx
    @0
    cz
    cZ
    @5
    @0
    wceq
    #
    @6
    c1
    c1
    cle
    @8
    @6
    @0
    cabs
    cfv
    #
    c1
    @5
    @0
    cabs
    fveq2
    @9
    c1
    cabs
    cfv
    #
    c1
    c1
    ax-1cn
    absnegi
    abs1
    eqtri
    syl6eq
    breq1d
    lgslem2.z
    elrab2
    mpbir2an
    @2
    cc0
    cz
    wcel
    cc0
    c1
    cle
    wbr
    #
    0z
    0le1
    @7
    @11
    vx
    cc0
    cz
    cZ
    @5
    cc0
    wceq
    #
    @6
    cc0
    c1
    cle
    @12
    @6
    cc0
    cabs
    cfv
    cc0
    @5
    cc0
    cabs
    fveq2
    abs0
    syl6eq
    breq1d
    lgslem2.z
    elrab2
    mpbir2an
    @3
    c1
    cz
    wcel
    @4
    1z
    1le1
    @7
    @4
    vx
    c1
    cz
    cZ
    @5
    c1
    wceq
    #
    @6
    c1
    c1
    cle
    @13
    @6
    @10
    c1
    @5
    c1
    cabs
    fveq2
    abs1
    syl6eq
    breq1d
    lgslem2.z
    elrab2
    mpbir2an
    3pm3.2i
end
