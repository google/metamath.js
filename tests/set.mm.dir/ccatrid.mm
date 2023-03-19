include "cword.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "c0.mm"
include "cconcat.mm"
include "wfn.mm"
include "caddc.mm"
include "wrd0.mm"
include "ccatvalfn.mm"
include "mpan2.mm"
include "hash0.mm"
include "oveq2i.mm"
include "lencl.mm"
include "nn0cnd.mm"
include "addid1d.mm"
include "syl5req.mm"
include "oveq2d.mm"
include "fneq2d.mm"
include "mpbird.mm"
include "wrdfn.mm"
include "cv.mm"
include "wceq.mm"
include "ccatval1.mm"
include "mp3an2.mm"
include "eqfnfvd.mm"

theorem ccatrid
  let cB: class B
  let cS: class S
  let vx: setvar x
  let cT: class T
  let cU: class U


  assert |- ( S e. Word B -> ( S ++ (/) ) = S )

  proof
    cS
    cB
    cword
    #
    wcel
    #
    vx
    cc0
    cS
    chash
    cfv
    #
    cfzo
    co
    #
    cS
    c0
    cconcat
    co
    #
    cS
    @1
    @4
    @3
    wfn
    @4
    cc0
    @2
    c0
    chash
    cfv
    #
    caddc
    co
    #
    cfzo
    co
    #
    wfn
    #
    @1
    c0
    @0
    wcel
    #
    @8
    cB
    wrd0
    #
    cS
    c0
    cB
    ccatvalfn
    mpan2
    @1
    @3
    @7
    @4
    @1
    @2
    @6
    cc0
    cfzo
    @1
    @6
    @2
    cc0
    caddc
    co
    @2
    @5
    cc0
    @2
    caddc
    hash0
    oveq2i
    @1
    @2
    @1
    @2
    cB
    cS
    lencl
    nn0cnd
    addid1d
    syl5req
    oveq2d
    fneq2d
    mpbird
    cB
    cS
    wrdfn
    @1
    @9
    vx
    cv
    #
    @3
    wcel
    @11
    @4
    cfv
    @11
    cS
    cfv
    wceq
    @10
    cB
    cS
    c0
    @11
    ccatval1
    mp3an2
    eqfnfvd
end
