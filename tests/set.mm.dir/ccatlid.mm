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
include "mpan.mm"
include "hash0.mm"
include "oveq1i.mm"
include "lencl.mm"
include "nn0cnd.mm"
include "addid2d.mm"
include "syl5eq.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "fneq2d.mm"
include "mpbird.mm"
include "wrdfn.mm"
include "cv.mm"
include "wa.mm"
include "cmin.mm"
include "wceq.mm"
include "a1i.mm"
include "oveq12d.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "ccatval2.mm"
include "mp3an1.mm"
include "syldan.mm"
include "oveq2i.mm"
include "cz.mm"
include "elfzoelz.mm"
include "adantl.mm"
include "zcnd.mm"
include "subid1d.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "eqfnfvd.mm"

theorem ccatlid
  let cB: class B
  let cS: class S
  let vx: setvar x
  let cT: class T
  let cU: class U


  assert |- ( S e. Word B -> ( (/) ++ S ) = S )

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
    c0
    cS
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
    c0
    chash
    cfv
    #
    @2
    caddc
    co
    #
    cfzo
    co
    #
    wfn
    #
    c0
    @0
    wcel
    #
    @1
    @8
    cB
    wrd0
    #
    c0
    cS
    cB
    ccatvalfn
    mpan
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
    @1
    @6
    cc0
    @2
    caddc
    co
    @2
    @5
    cc0
    @2
    caddc
    hash0
    oveq1i
    @1
    @2
    @1
    @2
    cB
    cS
    lencl
    nn0cnd
    addid2d
    syl5eq
    #
    eqcomd
    oveq2d
    fneq2d
    mpbird
    cB
    cS
    wrdfn
    @1
    vx
    cv
    #
    @3
    wcel
    #
    wa
    #
    @12
    @4
    cfv
    #
    @12
    @5
    cmin
    co
    #
    cS
    cfv
    #
    @12
    cS
    cfv
    @1
    @13
    @12
    @5
    @6
    cfzo
    co
    #
    wcel
    #
    @15
    @17
    wceq
    #
    @1
    @19
    @13
    @1
    @18
    @3
    @12
    @1
    @5
    cc0
    @6
    @2
    cfzo
    @5
    cc0
    wceq
    @1
    hash0
    a1i
    @11
    oveq12d
    eleq2d
    biimpar
    @9
    @1
    @19
    @20
    @10
    cB
    c0
    cS
    @12
    ccatval2
    mp3an1
    syldan
    @14
    @16
    @12
    cS
    @14
    @16
    @12
    cc0
    cmin
    co
    @12
    @5
    cc0
    @12
    cmin
    hash0
    oveq2i
    @14
    @12
    @14
    @12
    @13
    @12
    cz
    wcel
    @1
    @12
    cc0
    @2
    elfzoelz
    adantl
    zcnd
    subid1d
    syl5eq
    fveq2d
    eqtrd
    eqfnfvd
end
