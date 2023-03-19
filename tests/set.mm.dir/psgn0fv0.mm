include "c0.mm"
include "cvv.mm"
include "wcel.mm"
include "cpmtr.mm"
include "cfv.mm"
include "crn.mm"
include "cword.mm"
include "cpsgn.mm"
include "c1.mm"
include "wceq.mm"
include "0ex.mm"
include "wrd0.mm"
include "wa.mm"
include "csymg.mm"
include "cgsu.mm"
include "co.mm"
include "cneg.mm"
include "chash.mm"
include "cexp.mm"
include "c0g.mm"
include "eqid.mm"
include "gsum0.mm"
include "cid.mm"
include "cres.mm"
include "symgid.mm"
include "ax-mp.mm"
include "res0.mm"
include "eqtr3i.mm"
include "a1i.mm"
include "syl5req.mm"
include "fveq2d.mm"
include "psgnvalii.mm"
include "cc0.mm"
include "hash0.mm"
include "oveq2i.mm"
include "cc.mm"
include "neg1cn.mm"
include "exp0.mm"
include "eqtri.mm"
include "3eqtrd.mm"
include "mp2an.mm"

theorem psgn0fv0



  assert |- ( ( pmSgn ` (/) ) ` (/) ) = 1

  proof
    c0
    cvv
    wcel
    #
    c0
    c0
    cpmtr
    cfv
    crn
    #
    cword
    wcel
    #
    c0
    c0
    cpsgn
    cfv
    #
    cfv
    #
    c1
    wceq
    0ex
    @1
    wrd0
    @0
    @2
    wa
    #
    @4
    c0
    csymg
    cfv
    #
    c0
    cgsu
    co
    #
    @3
    cfv
    c1
    cneg
    #
    c0
    chash
    cfv
    #
    cexp
    co
    #
    c1
    @5
    c0
    @7
    @3
    @5
    @7
    @6
    c0g
    cfv
    #
    c0
    @6
    @11
    @11
    eqid
    gsum0
    @11
    c0
    wceq
    @5
    cid
    c0
    cres
    #
    @11
    c0
    @0
    @12
    @11
    wceq
    0ex
    c0
    @6
    cvv
    @6
    eqid
    #
    symgid
    ax-mp
    cid
    res0
    eqtr3i
    a1i
    syl5req
    fveq2d
    c0
    @1
    @6
    @3
    cvv
    c0
    @13
    @1
    eqid
    @3
    eqid
    psgnvalii
    @10
    c1
    wceq
    @5
    @10
    @8
    cc0
    cexp
    co
    #
    c1
    @9
    cc0
    @8
    cexp
    hash0
    oveq2i
    @8
    cc
    wcel
    @14
    c1
    wceq
    neg1cn
    @8
    exp0
    ax-mp
    eqtri
    a1i
    3eqtrd
    mp2an
end
