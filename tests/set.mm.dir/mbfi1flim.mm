include "cn.mm"
include "citg1.mm"
include "cdm.mm"
include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "cmpt.mm"
include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cif.mm"
include "cli.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "cvv.mm"
include "cvol.mm"
include "wss.mm"
include "cmbf.mm"
include "iftrue.mm"
include "mpteq2ia.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "syl5eqel.mm"
include "fvex.mm"
include "c0ex.mm"
include "ifex.mm"
include "a1i.mm"
include "mbfdm2.mm"
include "mblss.mm"
include "syl.mm"
include "rembl.mm"
include "cdif.mm"
include "wn.mm"
include "eldifn.mm"
include "adantl.mm"
include "iffalsed.mm"
include "mbfss.mm"
include "ffvelrnda.mm"
include "0red.mm"
include "ifclda.mm"
include "adantr.mm"
include "eqid.mm"
include "fmptd.mm"
include "mbfi1flimlem.mm"
include "wi.mm"
include "ssralv.mm"
include "wceq.mm"
include "sselda.mm"
include "eleq1.mm"
include "fveq2.mm"
include "ifbieq1d.mm"
include "fvmpt.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "ralbidva.mm"
include "sylibd.mm"
include "anim2d.mm"
include "eximdv.mm"
include "mpd.mm"

theorem mbfi1flim
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let vg: setvar g
  let vn: setvar n
  let cF: class F
  let vy: setvar y
  let vf: setvar f
  let vh: setvar h
  let vk: setvar k
  assume mbfi1flim.1: |- ( ph -> F e. MblFn )
  assume mbfi1flim.2: |- ( ph -> F : A --> RR )

  disjoint g n
  disjoint g x
  disjoint A g
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint F g
  disjoint F n
  disjoint F x
  disjoint g ph
  disjoint n ph
  disjoint ph x
  disjoint g y
  disjoint n y
  disjoint x y
  disjoint A y
  disjoint f g
  disjoint f h
  disjoint f k
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint F f
  disjoint g h
  disjoint g k
  disjoint h k
  disjoint h n
  disjoint h x
  disjoint h y
  disjoint F h
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint F k
  disjoint F y
  disjoint f ph
  disjoint h ph
  disjoint k ph
  disjoint ph y
  assert |- ( ph -> E. g ( g : NN --> dom S.1 /\ A. x e. A ( n e. NN |-> ( ( g ` n ) ` x ) ) ~~> ( F ` x ) ) )

  proof
    wph
    cn
    citg1
    cdm
    vg
    cv
    #
    wf
    #
    vn
    cn
    vx
    cv
    #
    vn
    cv
    @0
    cfv
    cfv
    cmpt
    #
    @2
    vy
    cr
    vy
    cv
    #
    cA
    wcel
    #
    @4
    cF
    cfv
    #
    cc0
    cif
    #
    cmpt
    #
    cfv
    #
    cli
    wbr
    #
    vx
    cr
    wral
    #
    wa
    #
    vg
    wex
    @1
    @3
    @2
    cF
    cfv
    #
    cli
    wbr
    #
    vx
    cA
    wral
    #
    wa
    #
    vg
    wex
    wph
    vx
    vg
    vn
    @8
    wph
    vy
    cA
    cr
    @7
    cvv
    wph
    cA
    cvol
    cdm
    #
    wcel
    cA
    cr
    wss
    #
    wph
    vy
    cA
    @7
    cvv
    wph
    vy
    cA
    @7
    cmpt
    vy
    cA
    @6
    cmpt
    #
    cmbf
    vy
    cA
    @7
    @6
    @5
    @6
    cc0
    iftrue
    mpteq2ia
    wph
    cF
    @19
    cmbf
    wph
    vy
    cA
    cr
    cF
    mbfi1flim.2
    feqmptd
    mbfi1flim.1
    eqeltrrd
    syl5eqel
    #
    @7
    cvv
    wcel
    wph
    @5
    wa
    @5
    @6
    cc0
    @4
    cF
    fvex
    c0ex
    ifex
    a1i
    #
    mbfdm2
    cA
    mblss
    syl
    #
    cr
    @17
    wcel
    wph
    rembl
    a1i
    @21
    wph
    @4
    cr
    cA
    cdif
    wcel
    #
    wa
    @5
    @6
    cc0
    @23
    @5
    wn
    #
    wph
    @4
    cr
    cA
    eldifn
    adantl
    iffalsed
    @20
    mbfss
    wph
    vy
    cr
    @7
    cr
    @8
    wph
    @7
    cr
    wcel
    @4
    cr
    wcel
    wph
    @5
    @6
    cc0
    cr
    wph
    cA
    cr
    @4
    cF
    mbfi1flim.2
    ffvelrnda
    wph
    @24
    wa
    0red
    ifclda
    adantr
    @8
    eqid
    #
    fmptd
    mbfi1flimlem
    wph
    @12
    @16
    vg
    wph
    @11
    @15
    @1
    wph
    @11
    @10
    vx
    cA
    wral
    #
    @15
    wph
    @18
    @11
    @26
    wi
    @22
    @10
    vx
    cA
    cr
    ssralv
    syl
    wph
    @10
    @14
    vx
    cA
    wph
    @2
    cA
    wcel
    #
    wa
    #
    @9
    @13
    @3
    cli
    @28
    @9
    @27
    @13
    cc0
    cif
    #
    @13
    @28
    @2
    cr
    wcel
    @9
    @29
    wceq
    wph
    cA
    cr
    @2
    @22
    sselda
    vy
    @2
    @7
    @29
    cr
    @8
    @4
    @2
    wceq
    @5
    @27
    @6
    @13
    cc0
    @4
    @2
    cA
    eleq1
    @4
    @2
    cF
    fveq2
    ifbieq1d
    @25
    @27
    @13
    cc0
    @2
    cF
    fvex
    c0ex
    ifex
    fvmpt
    syl
    @27
    @29
    @13
    wceq
    wph
    @27
    @13
    cc0
    iftrue
    adantl
    eqtrd
    breq2d
    ralbidva
    sylibd
    anim2d
    eximdv
    mpd
end
