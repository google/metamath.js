include "cvv.mm"
include "wcel.mm"
include "cress.mm"
include "co.mm"
include "csca.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cnx.mm"
include "cop.mm"
include "csts.mm"
include "cvsca.mm"
include "cmulr.mm"
include "cip.mm"
include "scaid.mm"
include "wne.mm"
include "c5.mm"
include "c6.mm"
include "5re.mm"
include "5lt6.mm"
include "ltneii.mm"
include "scandx.mm"
include "vscandx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "c8.mm"
include "5lt8.mm"
include "ipndx.mm"
include "eqtri.mm"
include "ovexd.mm"
include "setsid.mm"
include "sylan2.mm"
include "csra.mm"
include "adantl.mm"
include "cbs.mm"
include "wss.mm"
include "sraval.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "wn.mm"
include "c0.mm"
include "str0.mm"
include "reldmress.mm"
include "ovprc1.mm"
include "adantr.mm"
include "fvprc.mm"
include "fveq1d.mm"
include "0fv.mm"
include "syl6eq.mm"
include "sylan9eqr.mm"
include "pm2.61ian.mm"

theorem srasca
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cW: class W
  let vs: setvar s
  let cV: class V
  let vw: setvar w
  assume srapart.a: |- ( ph -> A = ( ( subringAlg ` W ) ` S ) )
  assume srapart.s: |- ( ph -> S C_ ( Base ` W ) )


  assert |- ( ph -> ( W |`s S ) = ( Scalar ` A ) )

  proof
    cW
    cvv
    wcel
    #
    wph
    cW
    cS
    cress
    co
    #
    cA
    csca
    cfv
    #
    wceq
    @0
    wph
    wa
    #
    cW
    cnx
    csca
    cfv
    #
    @1
    cop
    csts
    co
    #
    csca
    cfv
    #
    @5
    cnx
    cvsca
    cfv
    #
    cW
    cmulr
    cfv
    #
    cop
    csts
    co
    #
    cnx
    cip
    cfv
    #
    @8
    cop
    csts
    co
    #
    csca
    cfv
    #
    @1
    @2
    @6
    @9
    csca
    cfv
    @12
    @8
    @7
    csca
    @5
    scaid
    @4
    @7
    wne
    c5
    c6
    wne
    c5
    c6
    5re
    5lt6
    ltneii
    @4
    c5
    @7
    c6
    scandx
    vscandx
    neeq12i
    mpbir
    setsnid
    @8
    @10
    csca
    @9
    scaid
    @4
    @10
    wne
    c5
    c8
    wne
    c5
    c8
    5re
    5lt8
    ltneii
    @4
    c5
    @10
    c8
    scandx
    ipndx
    neeq12i
    mpbir
    setsnid
    eqtri
    wph
    @0
    @1
    cvv
    wcel
    @1
    @6
    wceq
    wph
    cW
    cS
    cress
    ovexd
    cvv
    @1
    csca
    cvv
    cW
    scaid
    setsid
    sylan2
    @3
    cA
    @11
    csca
    @3
    cA
    cS
    cW
    csra
    cfv
    #
    cfv
    #
    @11
    wph
    cA
    @14
    wceq
    @0
    srapart.a
    adantl
    wph
    @0
    cS
    cW
    cbs
    cfv
    wss
    @14
    @11
    wceq
    srapart.s
    cS
    cvv
    cW
    sraval
    sylan2
    eqtrd
    fveq2d
    3eqtr4a
    @0
    wn
    #
    wph
    wa
    #
    c0
    c0
    csca
    cfv
    @1
    @2
    csca
    @4
    scaid
    str0
    @15
    @1
    c0
    wceq
    wph
    cW
    cS
    cress
    reldmress
    ovprc1
    adantr
    @16
    cA
    c0
    csca
    wph
    @15
    cA
    @14
    c0
    srapart.a
    @15
    @14
    cS
    c0
    cfv
    c0
    @15
    cS
    @13
    c0
    cW
    csra
    fvprc
    fveq1d
    cS
    0fv
    syl6eq
    sylan9eqr
    fveq2d
    3eqtr4a
    pm2.61ian
end
