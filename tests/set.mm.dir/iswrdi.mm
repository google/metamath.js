include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cn0.mm"
include "wrex.mm"
include "cword.mm"
include "wcel.mm"
include "wceq.mm"
include "oveq2.mm"
include "feq2d.mm"
include "rspcev.mm"
include "wn.mm"
include "wa.mm"
include "0nn0.mm"
include "c0.mm"
include "wne.mm"
include "cn.mm"
include "fzo0n0.mm"
include "nnnn0.mm"
include "sylbi.mm"
include "necon1bi.mm"
include "fzo0.mm"
include "syl6eqr.mm"
include "biimpa.mm"
include "sylancr.mm"
include "pm2.61ian.mm"
include "iswrd.mm"
include "sylibr.mm"

theorem iswrdi
  let cS: class S
  let cL: class L
  let cW: class W
  let vl: setvar l


  assert |- ( W : ( 0 ..^ L ) --> S -> W e. Word S )

  proof
    cc0
    cL
    cfzo
    co
    #
    cS
    cW
    wf
    #
    cc0
    vl
    cv
    #
    cfzo
    co
    #
    cS
    cW
    wf
    #
    vl
    cn0
    wrex
    #
    cW
    cS
    cword
    wcel
    cL
    cn0
    wcel
    #
    @1
    @5
    @4
    @1
    vl
    cL
    cn0
    @2
    cL
    wceq
    @3
    @0
    cS
    cW
    @2
    cL
    cc0
    cfzo
    oveq2
    feq2d
    rspcev
    @6
    wn
    #
    @1
    wa
    cc0
    cn0
    wcel
    cc0
    cc0
    cfzo
    co
    #
    cS
    cW
    wf
    #
    @5
    0nn0
    @7
    @1
    @9
    @7
    @0
    @8
    cS
    cW
    @7
    @0
    c0
    @8
    @6
    @0
    c0
    @0
    c0
    wne
    cL
    cn
    wcel
    @6
    cL
    fzo0n0
    cL
    nnnn0
    sylbi
    necon1bi
    cc0
    fzo0
    syl6eqr
    feq2d
    biimpa
    @4
    @9
    vl
    cc0
    cn0
    @2
    cc0
    wceq
    @3
    @8
    cS
    cW
    @2
    cc0
    cc0
    cfzo
    oveq2
    feq2d
    rspcev
    sylancr
    pm2.61ian
    cS
    cW
    vl
    iswrd
    sylibr
end
