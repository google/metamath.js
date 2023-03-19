include "cfth.mm"
include "co.mm"
include "wbr.mm"
include "cfunc.mm"
include "cv.mm"
include "ccnv.mm"
include "wfun.mm"
include "wral.mm"
include "fthfunc.mm"
include "ssbri.mm"
include "wa.mm"
include "copab.mm"
include "ccat.mm"
include "wcel.mm"
include "wceq.mm"
include "cop.mm"
include "df-br.mm"
include "funcrcl.mm"
include "sylbi.mm"
include "cbs.mm"
include "cfv.mm"
include "oveq12.mm"
include "breqd.mm"
include "simpl.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "raleqdv.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "opabbidv.mm"
include "df-fth.mm"
include "ovex.mm"
include "ssopab2i.mm"
include "opabss.mm"
include "sstri.mm"
include "ssexi.mm"
include "ovmpt2a.mm"
include "syl.mm"
include "cvv.mm"
include "wb.mm"
include "wrel.mm"
include "relfunc.mm"
include "brrelex12.mm"
include "mpan.mm"
include "breq12.mm"
include "simpr.mm"
include "oveqd.mm"
include "cnveqd.mm"
include "funeqd.mm"
include "2ralbidv.mm"
include "eqid.mm"
include "brabga.mm"
include "bitrd.mm"
include "bianabs.mm"
include "biadan2.mm"

theorem isfth
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  let vc: setvar c
  let vd: setvar d
  let vf: setvar f
  let vg: setvar g
  let wph: wff ph
  let cH: class H
  let cJ: class J
  let cX: class X
  let cY: class Y
  assume isfth.b: |- B = ( Base ` C )

  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint D x
  disjoint D y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint c d
  disjoint c f
  disjoint c g
  disjoint c x
  disjoint c y
  disjoint B c
  disjoint d f
  disjoint d g
  disjoint d x
  disjoint d y
  disjoint B d
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint C c
  disjoint C d
  disjoint C f
  disjoint C g
  disjoint D c
  disjoint D d
  disjoint D f
  disjoint D g
  disjoint ph x
  disjoint ph y
  disjoint F f
  disjoint F g
  disjoint G f
  disjoint G g
  disjoint H x
  disjoint H y
  disjoint J x
  disjoint J y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( F ( C Faith D ) G <-> ( F ( C Func D ) G /\ A. x e. B A. y e. B Fun `' ( x G y ) ) )

  proof
    cF
    cG
    cC
    cD
    cfth
    co
    #
    wbr
    #
    cF
    cG
    cC
    cD
    cfunc
    co
    #
    wbr
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    #
    ccnv
    #
    wfun
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @0
    @2
    cF
    cG
    cC
    cD
    fthfunc
    ssbri
    @3
    @1
    @9
    @3
    @1
    cF
    cG
    vf
    cv
    #
    vg
    cv
    #
    @2
    wbr
    #
    @4
    @5
    @11
    co
    #
    ccnv
    #
    wfun
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    wa
    #
    vf
    vg
    copab
    #
    wbr
    #
    @3
    @9
    wa
    #
    @3
    @0
    @19
    cF
    cG
    @3
    cC
    ccat
    wcel
    cD
    ccat
    wcel
    wa
    #
    @0
    @19
    wceq
    @3
    cF
    cG
    cop
    #
    @2
    wcel
    @22
    cF
    cG
    @2
    df-br
    cC
    cD
    @23
    funcrcl
    sylbi
    vc
    vd
    cC
    cD
    ccat
    ccat
    @10
    @11
    vc
    cv
    #
    vd
    cv
    #
    cfunc
    co
    #
    wbr
    #
    @15
    vy
    @24
    cbs
    cfv
    #
    wral
    #
    vx
    @28
    wral
    #
    wa
    #
    vf
    vg
    copab
    @19
    cfth
    @24
    cC
    wceq
    #
    @25
    cD
    wceq
    #
    wa
    #
    @31
    @18
    vf
    vg
    @34
    @27
    @12
    @30
    @17
    @34
    @26
    @2
    @10
    @11
    @24
    cC
    @25
    cD
    cfunc
    oveq12
    breqd
    @34
    @29
    @16
    vx
    @28
    cB
    @34
    @28
    cC
    cbs
    cfv
    cB
    @34
    @24
    cC
    cbs
    @32
    @33
    simpl
    fveq2d
    isfth.b
    syl6eqr
    #
    @34
    @15
    vy
    @28
    cB
    @35
    raleqdv
    raleqbidv
    anbi12d
    opabbidv
    vx
    vy
    vf
    vg
    vc
    vd
    df-fth
    @19
    @2
    cC
    cD
    cfunc
    ovex
    @19
    @12
    vf
    vg
    copab
    @2
    @18
    @12
    vf
    vg
    @12
    @17
    simpl
    ssopab2i
    vf
    vg
    @2
    opabss
    sstri
    ssexi
    ovmpt2a
    syl
    breqd
    @3
    cF
    cvv
    wcel
    cG
    cvv
    wcel
    wa
    #
    @20
    @21
    wb
    @2
    wrel
    @3
    @36
    cC
    cD
    relfunc
    cF
    cG
    @2
    brrelex12
    mpan
    @18
    @21
    vf
    vg
    cF
    cG
    @19
    cvv
    cvv
    @10
    cF
    wceq
    #
    @11
    cG
    wceq
    #
    wa
    #
    @12
    @3
    @17
    @9
    @10
    cF
    @11
    cG
    @2
    breq12
    @39
    @15
    @8
    vx
    vy
    cB
    cB
    @39
    @14
    @7
    @39
    @13
    @6
    @39
    @11
    cG
    @4
    @5
    @37
    @38
    simpr
    oveqd
    cnveqd
    funeqd
    2ralbidv
    anbi12d
    @19
    eqid
    brabga
    syl
    bitrd
    bianabs
    biadan2
end
