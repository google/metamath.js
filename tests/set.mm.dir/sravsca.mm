include "cvv.mm"
include "wcel.mm"
include "cmulr.mm"
include "cfv.mm"
include "cvsca.mm"
include "wceq.mm"
include "wa.mm"
include "cnx.mm"
include "csca.mm"
include "cress.mm"
include "co.mm"
include "cop.mm"
include "csts.mm"
include "cip.mm"
include "csra.mm"
include "adantl.mm"
include "cbs.mm"
include "wss.mm"
include "sraval.mm"
include "sylan2.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "ovex.mm"
include "fvex.mm"
include "vscaid.mm"
include "setsid.mm"
include "mp2an.mm"
include "wne.mm"
include "c6.mm"
include "c8.mm"
include "6re.mm"
include "6lt8.mm"
include "ltneii.mm"
include "vscandx.mm"
include "ipndx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "eqtri.mm"
include "syl6reqr.mm"
include "wn.mm"
include "c0.mm"
include "str0.mm"
include "fvprc.mm"
include "adantr.mm"
include "fveq1d.mm"
include "0fv.mm"
include "syl6eq.mm"
include "sylan9eqr.mm"
include "3eqtr4a.mm"
include "pm2.61ian.mm"

theorem sravsca
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cW: class W
  let vs: setvar s
  let cV: class V
  let vw: setvar w
  assume srapart.a: |- ( ph -> A = ( ( subringAlg ` W ) ` S ) )
  assume srapart.s: |- ( ph -> S C_ ( Base ` W ) )


  assert |- ( ph -> ( .r ` W ) = ( .s ` A ) )

  proof
    cW
    cvv
    wcel
    #
    wph
    cW
    cmulr
    cfv
    #
    cA
    cvsca
    cfv
    #
    wceq
    @0
    wph
    wa
    #
    @2
    cW
    cnx
    csca
    cfv
    cW
    cS
    cress
    co
    cop
    #
    csts
    co
    #
    cnx
    cvsca
    cfv
    #
    @1
    cop
    csts
    co
    #
    cnx
    cip
    cfv
    #
    @1
    cop
    csts
    co
    #
    cvsca
    cfv
    #
    @1
    @3
    cA
    @9
    cvsca
    @3
    cA
    cS
    cW
    csra
    cfv
    #
    cfv
    #
    @9
    wph
    cA
    @12
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
    @12
    @9
    wceq
    srapart.s
    cS
    cvv
    cW
    sraval
    sylan2
    eqtrd
    fveq2d
    @1
    @7
    cvsca
    cfv
    #
    @10
    @5
    cvv
    wcel
    @1
    cvv
    wcel
    @1
    @13
    wceq
    cW
    @4
    csts
    ovex
    cW
    cmulr
    fvex
    cvv
    @1
    cvsca
    cvv
    @5
    vscaid
    setsid
    mp2an
    @1
    @8
    cvsca
    @7
    vscaid
    @6
    @8
    wne
    c6
    c8
    wne
    c6
    c8
    6re
    6lt8
    ltneii
    @6
    c6
    @8
    c8
    vscandx
    ipndx
    neeq12i
    mpbir
    setsnid
    eqtri
    syl6reqr
    @0
    wn
    #
    wph
    wa
    #
    c0
    c0
    cvsca
    cfv
    @1
    @2
    cvsca
    @6
    vscaid
    str0
    @14
    @1
    c0
    wceq
    wph
    cW
    cmulr
    fvprc
    adantr
    @15
    cA
    c0
    cvsca
    wph
    @14
    cA
    @12
    c0
    srapart.a
    @14
    @12
    cS
    c0
    cfv
    c0
    @14
    cS
    @11
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
