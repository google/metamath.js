include "clinc.mm"
include "cvv.mm"
include "cv.mm"
include "csca.mm"
include "cfv.mm"
include "cbs.mm"
include "cmap.mm"
include "co.mm"
include "cpw.mm"
include "cvsca.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "cid.mm"
include "cres.mm"
include "cof.mm"
include "df-linc.mm"
include "wcel.mm"
include "wa.mm"
include "wfn.mm"
include "elmapfn.mm"
include "adantr.mm"
include "fnresi.mm"
include "a1i.mm"
include "vex.mm"
include "inidm.mm"
include "wel.mm"
include "eqidd.mm"
include "wceq.mm"
include "fvresi.mm"
include "adantl.mm"
include "offval.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "mpt2eq3ia.mm"
include "mpteq2i.mm"
include "eqtri.mm"

theorem dflinc2
  let vv: setvar v
  let vm: setvar m
  let vs: setvar s
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x

  disjoint m s
  disjoint m v
  disjoint s v
  disjoint i m
  disjoint i s
  disjoint i v
  disjoint k x
  assert |- linC = ( m e. _V |-> ( s e. ( ( Base ` ( Scalar ` m ) ) ^m v ) , v e. ~P ( Base ` m ) |-> ( m gsum ( s oF ( .s ` m ) ( _I |` v ) ) ) ) )

  proof
    clinc
    vm
    cvv
    vs
    vv
    vm
    cv
    #
    csca
    cfv
    cbs
    cfv
    #
    vv
    cv
    #
    cmap
    co
    #
    @0
    cbs
    cfv
    cpw
    #
    @0
    vi
    @2
    vi
    cv
    #
    vs
    cv
    #
    cfv
    #
    @5
    @0
    cvsca
    cfv
    #
    co
    cmpt
    #
    cgsu
    co
    #
    cmpt2
    #
    cmpt
    vm
    cvv
    vs
    vv
    @3
    @4
    @0
    @6
    cid
    @2
    cres
    #
    @8
    cof
    co
    #
    cgsu
    co
    #
    cmpt2
    #
    cmpt
    vi
    vv
    vm
    vs
    df-linc
    vm
    cvv
    @11
    @15
    vs
    vv
    @3
    @4
    @10
    @14
    @6
    @3
    wcel
    #
    @2
    @4
    wcel
    #
    wa
    #
    @9
    @13
    @0
    cgsu
    @18
    @13
    @9
    @18
    vi
    @2
    @2
    @7
    @5
    @8
    @2
    @6
    @12
    cvv
    cvv
    @16
    @6
    @2
    wfn
    @17
    @6
    @1
    @2
    elmapfn
    adantr
    @12
    @2
    wfn
    @18
    @2
    fnresi
    a1i
    @2
    cvv
    wcel
    @18
    vv
    vex
    a1i
    #
    @19
    @2
    inidm
    @18
    vi
    vv
    wel
    #
    wa
    @7
    eqidd
    @20
    @5
    @12
    cfv
    @5
    wceq
    @18
    @2
    @5
    fvresi
    adantl
    offval
    eqcomd
    oveq2d
    mpt2eq3ia
    mpteq2i
    eqtri
end
