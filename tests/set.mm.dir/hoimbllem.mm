include "cv.mm"
include "cfv.mm"
include "cico.mm"
include "co.mm"
include "cixp.mm"
include "cdif.mm"
include "ciin.mm"
include "hspdifhsp.mm"
include "cvoln.mm"
include "vonmea.mm"
include "dmmeasal.mm"
include "cfn.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "fict.mm"
include "syl.mm"
include "wa.mm"
include "csalg.mm"
include "adantr.mm"
include "cdm.mm"
include "simpr.mm"
include "cr.mm"
include "wf.mm"
include "ffvelrnd.mm"
include "hspmbl.mm"
include "wceq.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eleqtrd.mm"
include "ffvelrnda.mm"
include "saldifcl2.mm"
include "syl3anc.mm"
include "saliincl.mm"
include "eqeltrd.mm"

theorem hoimbllem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cS: class S
  let vi: setvar i
  let cH: class H
  let cX: class X
  let vl: setvar l
  let vk: setvar k
  assume hoimbllem.x: |- ( ph -> X e. Fin )
  assume hoimbllem.n: |- ( ph -> X =/= (/) )
  assume hoimbllem.s: |- S = dom ( voln ` X )
  assume hoimbllem.a: |- ( ph -> A : X --> RR )
  assume hoimbllem.b: |- ( ph -> B : X --> RR )
  assume hoimbllem.h: |- H = ( x e. Fin |-> ( l e. x , y e. RR |-> X_ i e. x if ( i = l , ( -oo (,) y ) , RR ) ) )

  disjoint A i
  disjoint A l
  disjoint A x
  disjoint A y
  disjoint i l
  disjoint i x
  disjoint i y
  disjoint l x
  disjoint l y
  disjoint x y
  disjoint B i
  disjoint B l
  disjoint B x
  disjoint B y
  disjoint H i
  disjoint H l
  disjoint H x
  disjoint H y
  disjoint S i
  disjoint X i
  disjoint X l
  disjoint X x
  disjoint X y
  disjoint i ph
  disjoint l ph
  disjoint ph x
  disjoint ph y
  disjoint k x
  assert |- ( ph -> X_ i e. X ( ( A ` i ) [,) ( B ` i ) ) e. S )

  proof
    wph
    vi
    cX
    vi
    cv
    #
    cA
    cfv
    #
    @0
    cB
    cfv
    #
    cico
    co
    cixp
    vi
    cX
    @0
    @2
    cX
    cH
    cfv
    #
    co
    #
    @0
    @1
    @3
    co
    #
    cdif
    #
    ciin
    cS
    wph
    vx
    vy
    cA
    cB
    vi
    cH
    cX
    vl
    hoimbllem.x
    hoimbllem.n
    hoimbllem.a
    hoimbllem.b
    hoimbllem.h
    hspdifhsp
    wph
    cS
    vi
    @6
    cX
    wph
    cS
    cX
    cvoln
    cfv
    #
    wph
    cX
    hoimbllem.x
    vonmea
    hoimbllem.s
    dmmeasal
    #
    wph
    cX
    cfn
    wcel
    #
    cX
    com
    cdom
    wbr
    hoimbllem.x
    cX
    fict
    syl
    hoimbllem.n
    wph
    @0
    cX
    wcel
    #
    wa
    #
    cS
    csalg
    wcel
    #
    @4
    cS
    wcel
    @5
    cS
    wcel
    @6
    cS
    wcel
    wph
    @12
    @10
    @8
    adantr
    @11
    @4
    @7
    cdm
    #
    cS
    @11
    vx
    vy
    vi
    cH
    @0
    cX
    @2
    vl
    hoimbllem.h
    wph
    @9
    @10
    hoimbllem.x
    adantr
    #
    wph
    @10
    simpr
    #
    @11
    cX
    cr
    @0
    cB
    wph
    cX
    cr
    cB
    wf
    @10
    hoimbllem.b
    adantr
    @15
    ffvelrnd
    hspmbl
    @13
    cS
    wceq
    @11
    cS
    @13
    hoimbllem.s
    eqcomi
    a1i
    #
    eleqtrd
    @11
    @5
    @13
    cS
    @11
    vx
    vy
    vi
    cH
    @0
    cX
    @1
    vl
    hoimbllem.h
    @14
    @15
    wph
    cX
    cr
    @0
    cA
    hoimbllem.a
    ffvelrnda
    hspmbl
    @16
    eleqtrd
    cS
    @4
    @5
    saldifcl2
    syl3anc
    saliincl
    eqeltrd
end
