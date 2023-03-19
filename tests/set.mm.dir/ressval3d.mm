include "wss.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "wceq.mm"
include "wn.mm"
include "wa.mm"
include "wo.mm"
include "wi.mm"
include "wpss.mm"
include "sspss.mm"
include "dfpss3.mm"
include "orbi1i.mm"
include "bitri.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cin.mm"
include "wcel.mm"
include "cvv.mm"
include "simplr.mm"
include "adantl.mm"
include "simpl.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "ssexg.mm"
include "syl2an.mm"
include "ressval2.mm"
include "syl3anc.mm"
include "df-ss.mm"
include "biimpi.mm"
include "eqcomd.mm"
include "adantr.mm"
include "opeq12d.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "ex.mm"
include "cress.mm"
include "oveq2.mm"
include "ressid.mm"
include "syl.mm"
include "3eqtrd.mm"
include "c1.mm"
include "df-base.mm"
include "1nn.mm"
include "cdm.mm"
include "syl5eqelr.mm"
include "setsidvald.mm"
include "syl6eq.mm"
include "jaoi.mm"
include "sylbi.mm"
include "mpcom.mm"

theorem ressval3d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cE: class E
  let cV: class V
  let cY: class Y
  assume ressval3d.r: |- R = ( S |`s A )
  assume ressval3d.b: |- B = ( Base ` S )
  assume ressval3d.e: |- E = ( Base ` ndx )
  assume ressval3d.s: |- ( ph -> S e. V )
  assume ressval3d.f: |- ( ph -> Fun S )
  assume ressval3d.d: |- ( ph -> E e. dom S )
  assume ressval3d.a: |- ( ph -> A e. Y )
  assume ressval3d.u: |- ( ph -> A C_ B )


  assert |- ( ph -> R = ( S sSet <. E , A >. ) )

  proof
    cA
    cB
    wss
    #
    wph
    cR
    cS
    cE
    cA
    cop
    #
    csts
    co
    #
    wceq
    #
    ressval3d.u
    @0
    @0
    cB
    cA
    wss
    wn
    #
    wa
    #
    cA
    cB
    wceq
    #
    wo
    #
    wph
    @3
    wi
    #
    @0
    cA
    cB
    wpss
    #
    @6
    wo
    @7
    cA
    cB
    sspss
    @9
    @5
    @6
    cA
    cB
    dfpss3
    orbi1i
    bitri
    @5
    @8
    @6
    @5
    wph
    @3
    @5
    wph
    wa
    #
    cR
    cS
    cnx
    cbs
    cfv
    #
    cA
    cB
    cin
    #
    cop
    #
    csts
    co
    #
    @2
    @10
    @4
    cS
    cV
    wcel
    #
    cA
    cvv
    wcel
    #
    cR
    @14
    wceq
    @0
    @4
    wph
    simplr
    wph
    @15
    @5
    ressval3d.s
    adantl
    @5
    @0
    cB
    cvv
    wcel
    #
    @16
    wph
    @0
    @4
    simpl
    @17
    wph
    cB
    cS
    cbs
    cfv
    #
    cvv
    ressval3d.b
    cS
    cbs
    fvex
    eqeltri
    a1i
    cA
    cB
    cvv
    ssexg
    syl2an
    cA
    cB
    cR
    cS
    cV
    cvv
    ressval3d.r
    ressval3d.b
    ressval2
    syl3anc
    @10
    @13
    @1
    cS
    csts
    @10
    @1
    @13
    @10
    cE
    @11
    cA
    @12
    cE
    @11
    wceq
    #
    @10
    ressval3d.e
    a1i
    @5
    cA
    @12
    wceq
    #
    wph
    @0
    @20
    @4
    @0
    @12
    cA
    @0
    @12
    cA
    wceq
    cA
    cB
    df-ss
    biimpi
    eqcomd
    adantr
    adantr
    opeq12d
    eqcomd
    oveq2d
    eqtrd
    ex
    @6
    wph
    @3
    @6
    wph
    wa
    #
    cR
    cS
    cS
    @11
    @18
    cop
    #
    csts
    co
    #
    @2
    @21
    cR
    cS
    cA
    cress
    co
    #
    cS
    cB
    cress
    co
    #
    cS
    cR
    @24
    wceq
    @21
    ressval3d.r
    a1i
    @6
    @24
    @25
    wceq
    wph
    cA
    cB
    cS
    cress
    oveq2
    adantr
    @21
    @15
    @25
    cS
    wceq
    wph
    @15
    @6
    ressval3d.s
    adantl
    cB
    cS
    cV
    ressval3d.b
    ressid
    syl
    3eqtrd
    wph
    cS
    @23
    wceq
    @6
    wph
    cS
    cbs
    c1
    cV
    df-base
    1nn
    ressval3d.s
    ressval3d.f
    wph
    @11
    cE
    cS
    cdm
    ressval3d.e
    ressval3d.d
    syl5eqelr
    setsidvald
    adantl
    @21
    @22
    @1
    cS
    csts
    @21
    @1
    @22
    @21
    cE
    @11
    cA
    @18
    @19
    @21
    ressval3d.e
    a1i
    @21
    cA
    cB
    @18
    @6
    wph
    simpl
    ressval3d.b
    syl6eq
    opeq12d
    eqcomd
    oveq2d
    3eqtrd
    ex
    jaoi
    sylbi
    mpcom
end
