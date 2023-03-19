include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "wn.mm"
include "wral.mm"
include "crab.mm"
include "c0.mm"
include "nfcv.mm"
include "c2.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "cpw.mm"
include "nfrab1.mm"
include "nfcxfr.mm"
include "nff.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "c1.mm"
include "wo.mm"
include "hashsn01.mm"
include "clt.mm"
include "2pos.mm"
include "0re.mm"
include "2re.mm"
include "ltnlei.mm"
include "mpbi.mm"
include "breq2.mm"
include "mtbiri.mm"
include "1lt2.mm"
include "1re.mm"
include "jaoi.mm"
include "ax-mp.mm"
include "fveq2.mm"
include "breq2d.mm"
include "lfgredgge2.mm"
include "nsyl3.mm"
include "ex.mm"
include "ralrimi.mm"
include "rabeq0.mm"
include "sylibr.mm"

theorem lfgrnloop
  let vx: setvar x
  let cA: class A
  let cU: class U
  let cE: class E
  let cG: class G
  let cI: class I
  let cV: class V
  let vy: setvar y
  let cX: class X
  assume lfuhgrnloopv.i: |- I = ( iEdg ` G )
  assume lfuhgrnloopv.a: |- A = dom I
  assume lfuhgrnloopv.e: |- E = { x e. ~P V | 2 <_ ( # ` x ) }

  disjoint A x
  disjoint I x
  disjoint V x
  disjoint U x
  disjoint I y
  disjoint x y
  disjoint V y
  disjoint X y
  assert |- ( I : A --> E -> { x e. A | ( I ` x ) = { U } } = (/) )

  proof
    cA
    cE
    cI
    wf
    #
    vx
    cv
    #
    cI
    cfv
    #
    cU
    csn
    #
    wceq
    #
    wn
    #
    vx
    cA
    wral
    @4
    vx
    cA
    crab
    c0
    wceq
    @0
    @5
    vx
    cA
    vx
    cA
    cE
    cI
    vx
    cI
    nfcv
    vx
    cA
    nfcv
    vx
    cE
    c2
    @1
    chash
    cfv
    cle
    wbr
    #
    vx
    cV
    cpw
    #
    crab
    lfuhgrnloopv.e
    @6
    vx
    @7
    nfrab1
    nfcxfr
    nff
    @0
    @1
    cA
    wcel
    #
    @5
    @4
    c2
    @2
    chash
    cfv
    #
    cle
    wbr
    #
    @0
    @8
    wa
    @4
    @10
    c2
    @3
    chash
    cfv
    #
    cle
    wbr
    #
    @11
    cc0
    wceq
    #
    @11
    c1
    wceq
    #
    wo
    @12
    wn
    #
    cU
    hashsn01
    @13
    @15
    @14
    @13
    @12
    c2
    cc0
    cle
    wbr
    #
    cc0
    c2
    clt
    wbr
    @16
    wn
    2pos
    cc0
    c2
    0re
    2re
    ltnlei
    mpbi
    @11
    cc0
    c2
    cle
    breq2
    mtbiri
    @14
    @12
    c2
    c1
    cle
    wbr
    #
    c1
    c2
    clt
    wbr
    @17
    wn
    1lt2
    c1
    c2
    1re
    2re
    ltnlei
    mpbi
    @11
    c1
    c2
    cle
    breq2
    mtbiri
    jaoi
    ax-mp
    @4
    @9
    @11
    c2
    cle
    @2
    @3
    chash
    fveq2
    breq2d
    mtbiri
    vx
    cA
    cE
    cG
    cI
    cV
    @1
    lfuhgrnloopv.i
    lfuhgrnloopv.a
    lfuhgrnloopv.e
    lfgredgge2
    nsyl3
    ex
    ralrimi
    @4
    vx
    cA
    rabeq0
    sylibr
end
