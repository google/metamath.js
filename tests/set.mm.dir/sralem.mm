include "cvv.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cnx.mm"
include "csca.mm"
include "cress.mm"
include "co.mm"
include "cop.mm"
include "csts.mm"
include "cvsca.mm"
include "cmulr.mm"
include "cip.mm"
include "csra.mm"
include "adantl.mm"
include "cbs.mm"
include "wss.mm"
include "sraval.mm"
include "sylan2.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "ndxid.mm"
include "wne.mm"
include "c5.mm"
include "clt.mm"
include "wbr.mm"
include "c8.mm"
include "wo.mm"
include "nnrei.mm"
include "5re.mm"
include "ltnei.mm"
include "necomd.mm"
include "5lt8.mm"
include "8re.mm"
include "lttri.mm"
include "mpan.mm"
include "syl.mm"
include "jaoi.mm"
include "ax-mp.mm"
include "ndxarg.mm"
include "scandx.mm"
include "neeq12i.mm"
include "mpbir.mm"
include "setsnid.mm"
include "c6.mm"
include "5lt6.mm"
include "6re.mm"
include "mpan2.mm"
include "6lt8.mm"
include "vscandx.mm"
include "ipndx.mm"
include "3eqtri.mm"
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

theorem sralem
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cE: class E
  let cN: class N
  let cW: class W
  let vs: setvar s
  let cV: class V
  let vw: setvar w
  assume srapart.a: |- ( ph -> A = ( ( subringAlg ` W ) ` S ) )
  assume srapart.s: |- ( ph -> S C_ ( Base ` W ) )
  assume sralem.1: |- E = Slot N
  assume sralem.2: |- N e. NN
  assume sralem.3: |- ( N < 5 \/ 8 < N )


  assert |- ( ph -> ( E ` W ) = ( E ` A ) )

  proof
    cW
    cvv
    wcel
    #
    wph
    cW
    cE
    cfv
    #
    cA
    cE
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
    #
    cW
    cS
    cress
    co
    #
    cop
    csts
    co
    #
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
    cE
    cfv
    #
    @1
    @3
    cA
    @11
    cE
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
    @1
    @6
    cE
    cfv
    @9
    cE
    cfv
    @12
    @5
    @4
    cE
    cW
    cE
    cN
    sralem.1
    sralem.2
    ndxid
    #
    cnx
    cE
    cfv
    #
    @4
    wne
    cN
    c5
    wne
    #
    cN
    c5
    clt
    wbr
    #
    c8
    cN
    clt
    wbr
    #
    wo
    #
    @17
    sralem.3
    @18
    @17
    @19
    @18
    c5
    cN
    cN
    c5
    cN
    sralem.2
    nnrei
    #
    5re
    ltnei
    necomd
    @19
    c5
    cN
    clt
    wbr
    #
    @17
    c5
    c8
    clt
    wbr
    #
    @19
    @22
    5lt8
    c5
    c8
    cN
    5re
    8re
    @21
    lttri
    mpan
    c5
    cN
    5re
    @21
    ltnei
    syl
    jaoi
    ax-mp
    @16
    cN
    @4
    c5
    cE
    cN
    sralem.1
    sralem.2
    ndxarg
    #
    scandx
    neeq12i
    mpbir
    setsnid
    @8
    @7
    cE
    @6
    @15
    @16
    @7
    wne
    cN
    c6
    wne
    #
    @20
    @25
    sralem.3
    @18
    @25
    @19
    @18
    c6
    cN
    @18
    cN
    c6
    clt
    wbr
    #
    c6
    cN
    wne
    @18
    c5
    c6
    clt
    wbr
    @26
    5lt6
    cN
    c5
    c6
    @21
    5re
    6re
    lttri
    mpan2
    cN
    c6
    @21
    6re
    ltnei
    syl
    necomd
    @19
    c6
    cN
    clt
    wbr
    #
    @25
    c6
    c8
    clt
    wbr
    @19
    @27
    6lt8
    c6
    c8
    cN
    6re
    8re
    @21
    lttri
    mpan
    c6
    cN
    6re
    @21
    ltnei
    syl
    jaoi
    ax-mp
    @16
    cN
    @7
    c6
    @24
    vscandx
    neeq12i
    mpbir
    setsnid
    @8
    @10
    cE
    @9
    @15
    @16
    @10
    wne
    cN
    c8
    wne
    #
    @20
    @28
    sralem.3
    @18
    @28
    @19
    @18
    c8
    cN
    @18
    cN
    c8
    clt
    wbr
    #
    c8
    cN
    wne
    @18
    @23
    @29
    5lt8
    cN
    c5
    c8
    @21
    5re
    8re
    lttri
    mpan2
    cN
    c8
    @21
    8re
    ltnei
    syl
    necomd
    c8
    cN
    8re
    @21
    ltnei
    jaoi
    ax-mp
    @16
    cN
    @10
    c8
    @24
    ipndx
    neeq12i
    mpbir
    setsnid
    3eqtri
    syl6reqr
    @0
    wn
    #
    wph
    wa
    #
    c0
    c0
    cE
    cfv
    @1
    @2
    cE
    cN
    sralem.1
    str0
    @30
    @1
    c0
    wceq
    wph
    cW
    cE
    fvprc
    adantr
    @31
    cA
    c0
    cE
    wph
    @30
    cA
    @14
    c0
    srapart.a
    @30
    @14
    cS
    c0
    cfv
    c0
    @30
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
