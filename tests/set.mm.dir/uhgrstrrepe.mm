include "cop.mm"
include "csts.mm"
include "co.mm"
include "cuhgr.mm"
include "wcel.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "cbs.mm"
include "setsvtx.mm"
include "syl6eqr.mm"
include "pweqd.mm"
include "difeq1d.mm"
include "feq3d.mm"
include "mpbird.mm"
include "setsiedg.mm"
include "dmeqd.mm"
include "feq12d.mm"
include "cvv.mm"
include "wb.mm"
include "ovex.mm"
include "eqid.mm"
include "isuhgr.mm"
include "mp1i.mm"

theorem uhgrstrrepe
  let wph: wff ph
  let cE: class E
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  assume uhgrstrrepe.v: |- V = ( Base ` G )
  assume uhgrstrrepe.i: |- I = ( .ef ` ndx )
  assume uhgrstrrepe.s: |- ( ph -> G Struct X )
  assume uhgrstrrepe.b: |- ( ph -> ( Base ` ndx ) e. dom G )
  assume uhgrstrrepe.w: |- ( ph -> E e. W )
  assume uhgrstrrepe.e: |- ( ph -> E : dom E --> ( ~P V \ { (/) } ) )


  assert |- ( ph -> ( G sSet <. I , E >. ) e. UHGraph )

  proof
    wph
    cG
    cI
    cE
    cop
    #
    csts
    co
    #
    cuhgr
    wcel
    #
    @1
    ciedg
    cfv
    #
    cdm
    #
    @1
    cvtx
    cfv
    #
    cpw
    #
    c0
    csn
    #
    cdif
    #
    @3
    wf
    #
    wph
    @9
    cE
    cdm
    #
    @8
    cE
    wf
    #
    wph
    @11
    @10
    cV
    cpw
    #
    @7
    cdif
    #
    cE
    wf
    uhgrstrrepe.e
    wph
    @8
    @13
    cE
    @10
    wph
    @6
    @12
    @7
    wph
    @5
    cV
    wph
    @5
    cG
    cbs
    cfv
    cV
    wph
    cE
    cG
    cI
    cW
    cX
    uhgrstrrepe.i
    uhgrstrrepe.s
    uhgrstrrepe.b
    uhgrstrrepe.w
    setsvtx
    uhgrstrrepe.v
    syl6eqr
    pweqd
    difeq1d
    feq3d
    mpbird
    wph
    @4
    @10
    @8
    @3
    cE
    wph
    cE
    cG
    cI
    cW
    cX
    uhgrstrrepe.i
    uhgrstrrepe.s
    uhgrstrrepe.b
    uhgrstrrepe.w
    setsiedg
    #
    wph
    @3
    cE
    @14
    dmeqd
    feq12d
    mpbird
    @1
    cvv
    wcel
    @2
    @9
    wb
    wph
    cG
    @0
    csts
    ovex
    cvv
    @3
    @1
    @5
    @5
    eqid
    @3
    eqid
    isuhgr
    mp1i
    mpbird
end
