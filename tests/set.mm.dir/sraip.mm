include "cvv.mm"
include "wcel.mm"
include "cmulr.mm"
include "cfv.mm"
include "cip.mm"
include "wceq.mm"
include "wa.mm"
include "cnx.mm"
include "csca.mm"
include "cress.mm"
include "co.mm"
include "cop.mm"
include "csts.mm"
include "cvsca.mm"
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
include "ipid.mm"
include "setsid.mm"
include "mp2an.mm"
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

theorem sraip
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cW: class W
  let vs: setvar s
  let cV: class V
  let vw: setvar w
  assume srapart.a: |- ( ph -> A = ( ( subringAlg ` W ) ` S ) )
  assume srapart.s: |- ( ph -> S C_ ( Base ` W ) )


  assert |- ( ph -> ( .r ` W ) = ( .i ` A ) )

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
    cip
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
    csts
    co
    #
    cnx
    cvsca
    cfv
    @1
    cop
    #
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
    cip
    cfv
    #
    @1
    @3
    cA
    @8
    cip
    @3
    cA
    cS
    cW
    csra
    cfv
    #
    cfv
    #
    @8
    wph
    cA
    @11
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
    @11
    @8
    wceq
    srapart.s
    cS
    cvv
    cW
    sraval
    sylan2
    eqtrd
    fveq2d
    @6
    cvv
    wcel
    @1
    cvv
    wcel
    @1
    @9
    wceq
    @4
    @5
    csts
    ovex
    cW
    cmulr
    fvex
    cvv
    @1
    cip
    cvv
    @6
    ipid
    setsid
    mp2an
    syl6reqr
    @0
    wn
    #
    wph
    wa
    #
    c0
    c0
    cip
    cfv
    @1
    @2
    cip
    @7
    ipid
    str0
    @12
    @1
    c0
    wceq
    wph
    cW
    cmulr
    fvprc
    adantr
    @13
    cA
    c0
    cip
    wph
    @12
    cA
    @11
    c0
    srapart.a
    @12
    @11
    cS
    c0
    cfv
    c0
    @12
    cS
    @10
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
