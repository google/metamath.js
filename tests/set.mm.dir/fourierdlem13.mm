include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "caddc.mm"
include "cv.mm"
include "cc0.mm"
include "cfz.mm"
include "cr.mm"
include "cmpt.mm"
include "a1i.mm"
include "wa.mm"
include "simpr.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "cmap.mm"
include "wcel.mm"
include "wf.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cfzo.mm"
include "wral.mm"
include "cn.mm"
include "wb.mm"
include "fourierdlem2.mm"
include "syl.mm"
include "mpbid.mm"
include "simpld.mm"
include "elmapi.mm"
include "ffvelrnd.mm"
include "resubcld.mm"
include "fvmptd.mm"
include "oveq2d.mm"
include "recnd.mm"
include "pncan3d.mm"
include "eqtr2d.mm"
include "jca.mm"

theorem fourierdlem13
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let vi: setvar i
  let vm: setvar m
  let cI: class I
  let cM: class M
  let cV: class V
  let cX: class X
  let vp: setvar p
  let vk: setvar k
  let vx: setvar x
  assume fourierdlem13.a: |- ( ph -> A e. RR )
  assume fourierdlem13.b: |- ( ph -> B e. RR )
  assume fourierdlem13.x: |- ( ph -> X e. RR )
  assume fourierdlem13.p: |- P = ( m e. NN |-> { p e. ( RR ^m ( 0 ... m ) ) | ( ( ( p ` 0 ) = ( A + X ) /\ ( p ` m ) = ( B + X ) ) /\ A. i e. ( 0 ..^ m ) ( p ` i ) < ( p ` ( i + 1 ) ) ) } )
  assume fourierdlem13.m: |- ( ph -> M e. NN )
  assume fourierdlem13.v: |- ( ph -> V e. ( P ` M ) )
  assume fourierdlem13.i: |- ( ph -> I e. ( 0 ... M ) )
  assume fourierdlem13.q: |- Q = ( i e. ( 0 ... M ) |-> ( ( V ` i ) - X ) )

  disjoint A m
  disjoint A p
  disjoint m p
  disjoint B m
  disjoint B p
  disjoint I i
  disjoint M i
  disjoint M m
  disjoint M p
  disjoint i m
  disjoint i p
  disjoint V i
  disjoint V p
  disjoint X i
  disjoint X m
  disjoint X p
  disjoint i ph
  disjoint k x
  assert |- ( ph -> ( ( Q ` I ) = ( ( V ` I ) - X ) /\ ( V ` I ) = ( X + ( Q ` I ) ) ) )

  proof
    wph
    cI
    cQ
    cfv
    #
    cI
    cV
    cfv
    #
    cX
    cmin
    co
    #
    wceq
    @1
    cX
    @0
    caddc
    co
    #
    wceq
    wph
    vi
    cI
    vi
    cv
    #
    cV
    cfv
    #
    cX
    cmin
    co
    #
    @2
    cc0
    cM
    cfz
    co
    #
    cQ
    cr
    cQ
    vi
    @7
    @6
    cmpt
    wceq
    wph
    fourierdlem13.q
    a1i
    wph
    @4
    cI
    wceq
    #
    wa
    #
    @5
    @1
    cX
    cmin
    @9
    @4
    cI
    cV
    wph
    @8
    simpr
    fveq2d
    oveq1d
    fourierdlem13.i
    wph
    @1
    cX
    wph
    @7
    cr
    cI
    cV
    wph
    cV
    cr
    @7
    cmap
    co
    wcel
    #
    @7
    cr
    cV
    wf
    wph
    @10
    cc0
    cV
    cfv
    cA
    cX
    caddc
    co
    #
    wceq
    cM
    cV
    cfv
    cB
    cX
    caddc
    co
    #
    wceq
    wa
    @5
    @4
    c1
    caddc
    co
    cV
    cfv
    clt
    wbr
    vi
    cc0
    cM
    cfzo
    co
    wral
    wa
    #
    wph
    cV
    cM
    cP
    cfv
    wcel
    #
    @10
    @13
    wa
    #
    fourierdlem13.v
    wph
    cM
    cn
    wcel
    @14
    @15
    wb
    fourierdlem13.m
    @11
    @12
    cP
    cV
    vi
    vm
    cM
    vp
    fourierdlem13.p
    fourierdlem2
    syl
    mpbid
    simpld
    cV
    cr
    @7
    elmapi
    syl
    fourierdlem13.i
    ffvelrnd
    #
    fourierdlem13.x
    resubcld
    fvmptd
    #
    wph
    @3
    cX
    @2
    caddc
    co
    @1
    wph
    @0
    @2
    cX
    caddc
    @17
    oveq2d
    wph
    cX
    @1
    wph
    cX
    fourierdlem13.x
    recnd
    wph
    @1
    @16
    recnd
    pncan3d
    eqtr2d
    jca
end
