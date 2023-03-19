include "cuhgr.mm"
include "wcel.mm"
include "c0.mm"
include "cdm.mm"
include "cvtx.mm"
include "cfv.mm"
include "cpw.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "f0.mm"
include "dm0.mm"
include "feq2i.mm"
include "mpbir.mm"
include "ciedg.mm"
include "wb.mm"
include "eqid.mm"
include "isuhgr.mm"
include "syl.mm"
include "wceq.mm"
include "id.mm"
include "dmeq.mm"
include "feq12d.mm"
include "bitrd.mm"
include "mpbiri.mm"

theorem uhgr0e
  let wph: wff ph
  let cG: class G
  let cW: class W
  assume uhgr0e.g: |- ( ph -> G e. W )
  assume uhgr0e.e: |- ( ph -> ( iEdg ` G ) = (/) )


  assert |- ( ph -> G e. UHGraph )

  proof
    wph
    cG
    cuhgr
    wcel
    #
    c0
    cdm
    #
    cG
    cvtx
    cfv
    #
    cpw
    c0
    csn
    cdif
    #
    c0
    wf
    #
    @4
    c0
    @3
    c0
    wf
    @3
    f0
    @1
    c0
    @3
    c0
    dm0
    feq2i
    mpbir
    wph
    @0
    cG
    ciedg
    cfv
    #
    cdm
    #
    @3
    @5
    wf
    #
    @4
    wph
    cG
    cW
    wcel
    @0
    @7
    wb
    uhgr0e.g
    cW
    @5
    cG
    @2
    @2
    eqid
    @5
    eqid
    isuhgr
    syl
    wph
    @5
    c0
    wceq
    #
    @7
    @4
    wb
    uhgr0e.e
    @8
    @6
    @1
    @3
    @5
    c0
    @8
    id
    @5
    c0
    dmeq
    feq12d
    syl
    bitrd
    mpbiri
end
