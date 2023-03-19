include "ctmt.mm"
include "cfv.mm"
include "cxps.mm"
include "co.mm"
include "cbs.mm"
include "cxmt.mm"
include "cxp.mm"
include "cres.mm"
include "wfn.mm"
include "wceq.mm"
include "cxme.mm"
include "eqid.mm"
include "wcel.mm"
include "tmsxms.mm"
include "syl.mm"
include "xpsdsfn2.mm"
include "fnresdm.mm"
include "xpsxms.mm"
include "syl2anc.mm"
include "xmsxmet2.mm"
include "eqeltrrd.mm"
include "tmsbas.mm"
include "xpeq12d.mm"
include "xpsbas.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "eleqtrrd.mm"

theorem tmsxps
  let wph: wff ph
  let cP: class P
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  assume tmsxps.p: |- P = ( dist ` ( ( toMetSp ` M ) Xs. ( toMetSp ` N ) ) )
  assume tmsxps.1: |- ( ph -> M e. ( *Met ` X ) )
  assume tmsxps.2: |- ( ph -> N e. ( *Met ` Y ) )


  assert |- ( ph -> P e. ( *Met ` ( X X. Y ) ) )

  proof
    wph
    cP
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
    cbs
    cfv
    #
    cxmt
    cfv
    #
    cX
    cY
    cxp
    #
    cxmt
    cfv
    wph
    cP
    @3
    @3
    cxp
    #
    cres
    #
    cP
    @4
    wph
    cP
    @6
    wfn
    @7
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
    @2
    eqid
    #
    @8
    eqid
    #
    @9
    eqid
    #
    wph
    cM
    cX
    cxmt
    cfv
    wcel
    #
    @0
    cxme
    wcel
    #
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
    wph
    cN
    cY
    cxmt
    cfv
    wcel
    #
    @1
    cxme
    wcel
    #
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
    tmsxps.p
    xpsdsfn2
    @6
    cP
    fnresdm
    syl
    wph
    @2
    cxme
    wcel
    #
    @7
    @4
    wcel
    wph
    @14
    @18
    @21
    @16
    @20
    @0
    @1
    @2
    @10
    xpsxms
    syl2anc
    cP
    @2
    @3
    @3
    eqid
    tmsxps.p
    xmsxmet2
    syl
    eqeltrrd
    wph
    @5
    @3
    cxmt
    wph
    @5
    @8
    @9
    cxp
    @3
    wph
    cX
    @8
    cY
    @9
    wph
    @13
    cX
    @8
    wceq
    tmsxps.1
    cM
    @0
    cX
    @15
    tmsbas
    syl
    wph
    @17
    cY
    @9
    wceq
    tmsxps.2
    cN
    @1
    cY
    @19
    tmsbas
    syl
    xpeq12d
    wph
    @0
    @1
    @2
    cxme
    cxme
    @8
    @9
    @10
    @11
    @12
    @16
    @20
    xpsbas
    eqtrd
    fveq2d
    eleqtrrd
end
