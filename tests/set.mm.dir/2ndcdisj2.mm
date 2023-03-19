include "wel.mm"
include "wrmo.mm"
include "wal.mm"
include "c2ndc.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "wa.mm"
include "wmo.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "df-rmo.mm"
include "albii.mm"
include "w3a.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "cvv.mm"
include "cdif.mm"
include "undif2.mm"
include "omex.mm"
include "peano1.mm"
include "snssi.mm"
include "ax-mp.mm"
include "ssdomg.mm"
include "mp2.mm"
include "wral.mm"
include "id.mm"
include "ssdif.mm"
include "dfss3.mm"
include "sylib.mm"
include "eldifi.mm"
include "anim1i.mm"
include "moimi.mm"
include "alimi.mm"
include "2ndcdisj.mm"
include "syl3an3br.mm"
include "syl3an.mm"
include "unctb.mm"
include "sylancr.mm"
include "syl5eqbrr.mm"
include "reldom.mm"
include "brrelexi.mm"
include "syl.mm"
include "ssun2.mm"
include "mpisyl.mm"
include "domtr.mm"
include "syl2anc.mm"
include "syl3an3b.mm"

theorem 2ndcdisj2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cJ: class J
  let vb: setvar b
  let vf: setvar f
  let vw: setvar w
  let vz: setvar z
  let vn: setvar n
  let cB: class B

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint J x
  disjoint b f
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint b n
  disjoint B b
  disjoint f n
  disjoint B f
  disjoint n w
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint J b
  disjoint J f
  assert |- ( ( J e. 2ndc /\ A C_ J /\ A. y E* x e. A y e. x ) -> A ~<_ _om )

  proof
    vy
    vx
    wel
    #
    vx
    cA
    wrmo
    #
    vy
    wal
    cJ
    c2ndc
    wcel
    #
    cA
    cJ
    wss
    #
    vx
    cv
    #
    cA
    wcel
    #
    @0
    wa
    #
    vx
    wmo
    #
    vy
    wal
    #
    cA
    com
    cdom
    wbr
    #
    @1
    @7
    vy
    @0
    vx
    cA
    df-rmo
    albii
    @2
    @3
    @8
    w3a
    #
    cA
    c0
    csn
    #
    cA
    cun
    #
    cdom
    wbr
    #
    @12
    com
    cdom
    wbr
    #
    @9
    @10
    @12
    cvv
    wcel
    #
    cA
    @12
    wss
    @13
    @10
    @14
    @15
    @10
    @12
    @11
    cA
    @11
    cdif
    #
    cun
    #
    com
    cdom
    @11
    cA
    undif2
    @10
    @11
    com
    cdom
    wbr
    #
    @16
    com
    cdom
    wbr
    #
    @17
    com
    cdom
    wbr
    com
    cvv
    wcel
    @11
    com
    wss
    #
    @18
    omex
    c0
    com
    wcel
    @20
    peano1
    c0
    com
    snssi
    ax-mp
    @11
    com
    cvv
    ssdomg
    mp2
    @2
    @2
    @3
    @4
    cJ
    @11
    cdif
    #
    wcel
    vx
    @16
    wral
    #
    @8
    @4
    @16
    wcel
    #
    @0
    wa
    #
    vx
    wmo
    #
    vy
    wal
    #
    @19
    @2
    id
    @3
    @16
    @21
    wss
    @22
    cA
    cJ
    @11
    ssdif
    vx
    @16
    @21
    dfss3
    sylib
    @7
    @25
    vy
    @24
    @6
    vx
    @23
    @5
    @0
    @4
    cA
    @11
    eldifi
    anim1i
    moimi
    alimi
    @26
    @2
    @22
    @0
    vx
    @16
    wrmo
    #
    vy
    wal
    @19
    @27
    @25
    vy
    @0
    vx
    @16
    df-rmo
    albii
    vx
    vy
    @16
    @4
    cJ
    2ndcdisj
    syl3an3br
    syl3an
    @11
    @16
    unctb
    sylancr
    syl5eqbrr
    #
    @12
    com
    cdom
    reldom
    brrelexi
    syl
    cA
    @11
    ssun2
    cA
    @12
    cvv
    ssdomg
    mpisyl
    @28
    cA
    @12
    com
    domtr
    syl2anc
    syl3an3b
end
