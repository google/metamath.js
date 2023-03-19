include "ctmt.mm"
include "cfv.mm"
include "cxps.mm"
include "co.mm"
include "ctopn.mm"
include "ctx.mm"
include "ctps.mm"
include "wcel.mm"
include "wceq.mm"
include "cxme.mm"
include "cxmt.mm"
include "eqid.mm"
include "tmsxms.mm"
include "syl.mm"
include "xmstps.mm"
include "xpstopn.mm"
include "syl2anc.mm"
include "cmopn.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "xpsxms.mm"
include "cds.mm"
include "reseq1i.mm"
include "xmstopn.mm"
include "wfn.mm"
include "xpsdsfn2.mm"
include "fnresdm.mm"
include "fveq2d.mm"
include "eqtr2d.mm"
include "syl5eq.mm"
include "tmstopn.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem tmsxpsmopn
  let wph: wff ph
  let cP: class P
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  assume tmsxps.p: |- P = ( dist ` ( ( toMetSp ` M ) Xs. ( toMetSp ` N ) ) )
  assume tmsxps.1: |- ( ph -> M e. ( *Met ` X ) )
  assume tmsxps.2: |- ( ph -> N e. ( *Met ` Y ) )
  assume tmsxpsmopn.j: |- J = ( MetOpen ` M )
  assume tmsxpsmopn.k: |- K = ( MetOpen ` N )
  assume tmsxpsmopn.l: |- L = ( MetOpen ` P )


  assert |- ( ph -> L = ( J tX K ) )

  proof
    wph
    cM
    ctmt
    cfv
    #
    cN
    ctmt
    cfv
    #
    cxps
    co
    #
    ctopn
    cfv
    #
    @0
    ctopn
    cfv
    #
    @1
    ctopn
    cfv
    #
    ctx
    co
    #
    cL
    cJ
    cK
    ctx
    co
    wph
    @0
    ctps
    wcel
    #
    @1
    ctps
    wcel
    #
    @3
    @6
    wceq
    wph
    @0
    cxme
    wcel
    #
    @7
    wph
    cM
    cX
    cxmt
    cfv
    wcel
    #
    @9
    tmsxps.1
    cM
    @0
    cX
    @0
    eqid
    #
    tmsxms
    syl
    #
    @0
    xmstps
    syl
    wph
    @1
    cxme
    wcel
    #
    @8
    wph
    cN
    cY
    cxmt
    cfv
    wcel
    #
    @13
    tmsxps.2
    cN
    @1
    cY
    @1
    eqid
    #
    tmsxms
    syl
    #
    @1
    xmstps
    syl
    @0
    @1
    @2
    @4
    @5
    @3
    @2
    eqid
    #
    @4
    eqid
    @5
    eqid
    @3
    eqid
    #
    xpstopn
    syl2anc
    wph
    cL
    cP
    cmopn
    cfv
    #
    @3
    tmsxpsmopn.l
    wph
    @3
    cP
    @2
    cbs
    cfv
    #
    @20
    cxp
    #
    cres
    #
    cmopn
    cfv
    #
    @19
    wph
    @2
    cxme
    wcel
    #
    @3
    @23
    wceq
    wph
    @9
    @13
    @24
    @12
    @16
    @0
    @1
    @2
    @17
    xpsxms
    syl2anc
    @22
    @3
    @2
    @20
    @18
    @20
    eqid
    cP
    @2
    cds
    cfv
    @21
    tmsxps.p
    reseq1i
    xmstopn
    syl
    wph
    @22
    cP
    cmopn
    wph
    cP
    @21
    wfn
    @22
    cP
    wceq
    wph
    cP
    @0
    @1
    @2
    cxme
    cxme
    @0
    cbs
    cfv
    #
    @1
    cbs
    cfv
    #
    @17
    @25
    eqid
    @26
    eqid
    @12
    @16
    tmsxps.p
    xpsdsfn2
    @21
    cP
    fnresdm
    syl
    fveq2d
    eqtr2d
    syl5eq
    wph
    cJ
    @4
    cK
    @5
    ctx
    wph
    @10
    cJ
    @4
    wceq
    tmsxps.1
    cM
    cJ
    @0
    cX
    @11
    tmsxpsmopn.j
    tmstopn
    syl
    wph
    @14
    cK
    @5
    wceq
    tmsxps.2
    cN
    cK
    @1
    cY
    @15
    tmsxpsmopn.k
    tmstopn
    syl
    oveq12d
    3eqtr4d
end
