include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cs1.mm"
include "wf.mm"
include "cfv.mm"
include "wceq.mm"
include "c0.mm"
include "cwlkson.mm"
include "wbr.mm"
include "cop.mm"
include "csn.mm"
include "s1val.mm"
include "cz.mm"
include "wa.mm"
include "wf1.mm"
include "0z.mm"
include "jctl.mm"
include "f1sng.mm"
include "f1f.mm"
include "3syl.mm"
include "id.mm"
include "fzsn.mm"
include "mp1i.mm"
include "feq12d.mm"
include "syl5ibrcom.mm"
include "mpd.mm"
include "s1fv.mm"
include "0wlkon.mm"
include "syl2anc.mm"

theorem 0wlkons1
  let cG: class G
  let cN: class N
  let cV: class V
  let vk: setvar k
  let cP: class P
  assume 0wlk.v: |- V = ( Vtx ` G )


  assert |- ( N e. V -> (/) ( N ( WalksOn ` G ) N ) <" N "> )

  proof
    cN
    cV
    wcel
    #
    cc0
    cc0
    cfz
    co
    #
    cV
    cN
    cs1
    #
    wf
    #
    cc0
    @2
    cfv
    cN
    wceq
    c0
    @2
    cN
    cN
    cG
    cwlkson
    cfv
    co
    wbr
    @0
    @2
    cc0
    cN
    cop
    csn
    #
    wceq
    #
    @3
    cN
    cV
    s1val
    @0
    @3
    @5
    cc0
    csn
    #
    cV
    @4
    wf
    #
    @0
    cc0
    cz
    wcel
    #
    @0
    wa
    @6
    cV
    @4
    wf1
    @7
    @0
    @8
    0z
    jctl
    cc0
    cN
    cz
    cV
    f1sng
    @6
    cV
    @4
    f1f
    3syl
    @5
    @1
    @6
    cV
    @2
    @4
    @5
    id
    @8
    @1
    @6
    wceq
    @5
    0z
    cc0
    fzsn
    mp1i
    feq12d
    syl5ibrcom
    mpd
    cN
    cV
    s1fv
    @2
    cG
    cN
    cV
    0wlk.v
    0wlkon
    syl2anc
end
