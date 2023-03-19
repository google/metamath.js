include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "c0.mm"
include "wne.mm"
include "cdm.mm"
include "cc0.mm"
include "chash.mm"
include "cfz.mm"
include "co.mm"
include "cvtx.mm"
include "wf.mm"
include "wceq.mm"
include "eqid.mm"
include "wlkp.mm"
include "fdm.mm"
include "eqcomd.mm"
include "syl.mm"
include "cn0.mm"
include "wcel.mm"
include "wlkcl.mm"
include "cuz.mm"
include "elnn0uz.mm"
include "fzn0.mm"
include "sylbb2.mm"
include "eqnetrrd.mm"
include "wrel.mm"
include "wb.mm"
include "frel.mm"
include "reldm0.mm"
include "necon3bid.mm"
include "mpbird.mm"

theorem wlkn0
  let cP: class P
  let cF: class F
  let cG: class G


  assert |- ( F ( Walks ` G ) P -> P =/= (/) )

  proof
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    #
    cP
    c0
    wne
    #
    cP
    cdm
    #
    c0
    wne
    #
    @0
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    #
    @2
    c0
    @0
    @5
    cG
    cvtx
    cfv
    #
    cP
    wf
    #
    @5
    @2
    wceq
    cP
    cF
    cG
    @6
    @6
    eqid
    wlkp
    #
    @7
    @2
    @5
    @5
    @6
    cP
    fdm
    eqcomd
    syl
    @0
    @4
    cn0
    wcel
    #
    @5
    c0
    wne
    #
    cP
    cF
    cG
    wlkcl
    @9
    @4
    cc0
    cuz
    cfv
    wcel
    @10
    @4
    elnn0uz
    cc0
    @4
    fzn0
    sylbb2
    syl
    eqnetrrd
    @0
    cP
    wrel
    #
    @1
    @3
    wb
    @0
    @7
    @11
    @8
    @5
    @6
    cP
    frel
    syl
    @11
    cP
    c0
    @2
    c0
    cP
    reldm0
    necon3bid
    syl
    mpbird
end
