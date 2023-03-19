include "cr.mm"
include "cv.mm"
include "wceq.mm"
include "cmnf.mm"
include "cioo.mm"
include "co.mm"
include "cif.mm"
include "cixp.mm"
include "cfv.mm"
include "cvv.mm"
include "cmpt2.mm"
include "cfn.mm"
include "cmpt.mm"
include "a1i.mm"
include "id.mm"
include "eqidd.mm"
include "ixpeq1.mm"
include "mpt2eq123dv.mm"
include "adantl.mm"
include "wcel.mm"
include "reex.mm"
include "eqid.mm"
include "mpt2exg.mm"
include "syl2anc.mm"
include "fvmptd.mm"
include "wa.mm"
include "simpl.mm"
include "eqeq2d.mm"
include "simpr.mm"
include "oveq2d.mm"
include "ifbieq1d.mm"
include "ixpeq2dv.mm"
include "wral.mm"
include "ovex.mm"
include "keepel.mm"
include "ralrimiva.mm"
include "ixpexg.mm"
include "syl.mm"
include "ovmpt2d.mm"

theorem hspval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vi: setvar i
  let vk: setvar k
  let cH: class H
  let cI: class I
  let cX: class X
  let cY: class Y
  assume hspval.h: |- H = ( x e. Fin |-> ( i e. x , y e. RR |-> X_ k e. x if ( k = i , ( -oo (,) y ) , RR ) ) )
  assume hspval.x: |- ( ph -> X e. Fin )
  assume hspval.i: |- ( ph -> I e. X )
  assume hspval.y: |- ( ph -> Y e. RR )

  disjoint I i
  disjoint I k
  disjoint I y
  disjoint i k
  disjoint i y
  disjoint k y
  disjoint X i
  disjoint X k
  disjoint X x
  disjoint X y
  disjoint i x
  disjoint k x
  disjoint x y
  disjoint Y i
  disjoint Y k
  disjoint Y y
  disjoint i ph
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( I ( H ` X ) Y ) = X_ k e. X if ( k = I , ( -oo (,) Y ) , RR ) )

  proof
    wph
    vi
    vy
    cI
    cY
    cX
    cr
    vk
    cX
    vk
    cv
    #
    vi
    cv
    #
    wceq
    #
    cmnf
    vy
    cv
    #
    cioo
    co
    #
    cr
    cif
    #
    cixp
    #
    vk
    cX
    @0
    cI
    wceq
    #
    cmnf
    cY
    cioo
    co
    #
    cr
    cif
    #
    cixp
    #
    cX
    cH
    cfv
    cvv
    wph
    vx
    cX
    vi
    vy
    vx
    cv
    #
    cr
    vk
    @11
    @5
    cixp
    #
    cmpt2
    #
    vi
    vy
    cX
    cr
    @6
    cmpt2
    #
    cfn
    cH
    cvv
    cH
    vx
    cfn
    @13
    cmpt
    wceq
    wph
    hspval.h
    a1i
    @11
    cX
    wceq
    #
    @13
    @14
    wceq
    wph
    @15
    vi
    vy
    @11
    cr
    @12
    cX
    cr
    @6
    @15
    id
    @15
    cr
    eqidd
    vk
    @11
    cX
    @5
    ixpeq1
    mpt2eq123dv
    adantl
    hspval.x
    wph
    cX
    cfn
    wcel
    cr
    cvv
    wcel
    #
    @14
    cvv
    wcel
    hspval.x
    @16
    wph
    reex
    a1i
    vi
    vy
    cX
    cr
    @6
    cfn
    cvv
    @14
    @14
    eqid
    mpt2exg
    syl2anc
    fvmptd
    @1
    cI
    wceq
    #
    @3
    cY
    wceq
    #
    wa
    #
    @6
    @10
    wceq
    wph
    @19
    vk
    cX
    @5
    @9
    @19
    @2
    @7
    @4
    @8
    cr
    @19
    @1
    cI
    @0
    @17
    @18
    simpl
    eqeq2d
    @19
    @3
    cY
    cmnf
    cioo
    @17
    @18
    simpr
    oveq2d
    ifbieq1d
    ixpeq2dv
    adantl
    hspval.i
    hspval.y
    wph
    @9
    cvv
    wcel
    #
    vk
    cX
    wral
    @10
    cvv
    wcel
    wph
    @20
    vk
    cX
    @20
    wph
    @0
    cX
    wcel
    wa
    @7
    @8
    cr
    cvv
    cmnf
    cY
    cioo
    ovex
    reex
    keepel
    a1i
    ralrimiva
    vk
    cX
    @9
    cvv
    ixpexg
    syl
    ovmpt2d
end
