include "cv.mm"
include "cc.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cim.mm"
include "csn.mm"
include "cin.mm"
include "cdif.mm"
include "ciun.mm"
include "cun.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "eqid.mm"
include "weq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "sneqd.mm"
include "cbviunv.mm"
include "uneq2i.mm"
include "infeq1i.mm"
include "cnrefiisplem.mm"
include "eleq1w.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "breq2d.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "rexbii.mm"
include "sylib.mm"

theorem cnrefiisp
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vz: setvar z
  let vk: setvar k
  assume cnrefiisp.a: |- ( ph -> A e. CC )
  assume cnrefiisp.n: |- ( ph -> -. A e. RR )
  assume cnrefiisp.b: |- ( ph -> B e. Fin )
  assume cnrefiisp.c: |- C = ( RR u. B )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint C x
  disjoint C y
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint A z
  disjoint w z
  disjoint x z
  disjoint B w
  disjoint B z
  disjoint C w
  disjoint ph w
  disjoint k x
  assert |- ( ph -> E. x e. RR+ A. y e. C ( ( y e. CC /\ y =/= A ) -> x <_ ( abs ` ( y - A ) ) ) )

  proof
    wph
    vw
    cv
    #
    cc
    wcel
    #
    @0
    cA
    wne
    #
    wa
    #
    vx
    cv
    #
    @0
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vw
    cC
    wral
    #
    vx
    crp
    wrex
    vy
    cv
    #
    cc
    wcel
    #
    @10
    cA
    wne
    #
    wa
    #
    @4
    @10
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    wi
    #
    vy
    cC
    wral
    #
    vx
    crp
    wrex
    wph
    vx
    vw
    cA
    cB
    cC
    cA
    cim
    cfv
    cabs
    cfv
    csn
    #
    vw
    cB
    cc
    cin
    cA
    csn
    cdif
    #
    @6
    csn
    #
    ciun
    #
    cun
    #
    @19
    vz
    @20
    vz
    cv
    #
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    csn
    #
    ciun
    #
    cun
    #
    cxr
    clt
    cinf
    cnrefiisp.a
    cnrefiisp.n
    cnrefiisp.b
    cnrefiisp.c
    @23
    eqid
    cxr
    @29
    @23
    clt
    @28
    @22
    @19
    vz
    vw
    @20
    @27
    @21
    vz
    vw
    weq
    #
    @26
    @6
    @30
    @25
    @5
    cabs
    @24
    @0
    cA
    cmin
    oveq1
    fveq2d
    sneqd
    cbviunv
    uneq2i
    infeq1i
    cnrefiisplem
    @9
    @18
    vx
    crp
    @8
    @17
    vw
    vy
    cC
    vw
    vy
    weq
    #
    @3
    @13
    @7
    @16
    @31
    @1
    @11
    @2
    @12
    vw
    vy
    cc
    eleq1w
    @0
    @10
    cA
    neeq1
    anbi12d
    @31
    @6
    @15
    @4
    cle
    @31
    @5
    @14
    cabs
    @0
    @10
    cA
    cmin
    oveq1
    fveq2d
    breq2d
    imbi12d
    cbvralv
    rexbii
    sylib
end
