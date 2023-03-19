include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cconcat.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cc0.mm"
include "caddc.mm"
include "cfzo.mm"
include "cv.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "ccatfval.mm"
include "fveq2d.mm"
include "wfn.mm"
include "wceq.mm"
include "fvex.mm"
include "ifex.mm"
include "eqid.mm"
include "fnmpti.mm"
include "hashfn.mm"
include "mp1i.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0addcl.mm"
include "syl2an.mm"
include "hashfzo0.mm"
include "syl.mm"
include "3eqtrd.mm"

theorem ccatlen
  let cB: class B
  let cS: class S
  let cT: class T
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x


  assert |- ( ( S e. Word B /\ T e. Word B ) -> ( # ` ( S ++ T ) ) = ( ( # ` S ) + ( # ` T ) ) )

  proof
    cS
    cB
    cword
    #
    wcel
    #
    cT
    @0
    wcel
    #
    wa
    #
    cS
    cT
    cconcat
    co
    #
    chash
    cfv
    vx
    cc0
    cS
    chash
    cfv
    #
    cT
    chash
    cfv
    #
    caddc
    co
    #
    cfzo
    co
    #
    vx
    cv
    #
    cc0
    @5
    cfzo
    co
    wcel
    #
    @9
    cS
    cfv
    #
    @9
    @5
    cmin
    co
    #
    cT
    cfv
    #
    cif
    #
    cmpt
    #
    chash
    cfv
    #
    @8
    chash
    cfv
    #
    @7
    @3
    @4
    @15
    chash
    vx
    cS
    cT
    @0
    @0
    ccatfval
    fveq2d
    @15
    @8
    wfn
    @16
    @17
    wceq
    @3
    vx
    @8
    @14
    @15
    @10
    @11
    @13
    @9
    cS
    fvex
    @12
    cT
    fvex
    ifex
    @15
    eqid
    fnmpti
    @8
    @15
    hashfn
    mp1i
    @3
    @7
    cn0
    wcel
    #
    @17
    @7
    wceq
    @1
    @5
    cn0
    wcel
    @6
    cn0
    wcel
    @18
    @2
    cB
    cS
    lencl
    cB
    cT
    lencl
    @5
    @6
    nn0addcl
    syl2an
    @7
    hashfzo0
    syl
    3eqtrd
end
