include "c1.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cn.mm"
include "wrex.mm"
include "cprime.mm"
include "wn.mm"
include "cvma.mm"
include "cfv.mm"
include "cc0.mm"
include "wcel.mm"
include "wa.mm"
include "1red.mm"
include "clt.mm"
include "wbr.mm"
include "c2.mm"
include "cuz.mm"
include "prmuz2.mm"
include "adantr.mm"
include "eluz2b2.mm"
include "sylib.mm"
include "simpld.mm"
include "nnred.mm"
include "cn0.mm"
include "nnnn0.mm"
include "adantl.mm"
include "reexpcld.mm"
include "simprd.mm"
include "cle.mm"
include "nncnd.mm"
include "exp1d.mm"
include "nnge1d.mm"
include "simpr.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "leexp2ad.mm"
include "eqbrtrrd.mm"
include "ltletrd.mm"
include "ltned.mm"
include "neneqd.mm"
include "nrexdv.mm"
include "nrex.mm"
include "wne.mm"
include "wb.mm"
include "1nn.mm"
include "isppw2.mm"
include "ax-mp.mm"
include "necon1bbii.mm"
include "mpbi.mm"

theorem vma1
  let vk: setvar k
  let vp: setvar p


  assert |- ( Lam ` 1 ) = 0

  proof
    c1
    vp
    cv
    #
    vk
    cv
    #
    cexp
    co
    #
    wceq
    #
    vk
    cn
    wrex
    #
    vp
    cprime
    wrex
    #
    wn
    c1
    cvma
    cfv
    #
    cc0
    wceq
    @4
    vp
    cprime
    @0
    cprime
    wcel
    #
    @3
    vk
    cn
    @7
    @1
    cn
    wcel
    #
    wa
    #
    c1
    @2
    @9
    c1
    @2
    @9
    1red
    #
    @9
    c1
    @0
    @2
    @10
    @9
    @0
    @9
    @0
    cn
    wcel
    #
    c1
    @0
    clt
    wbr
    #
    @9
    @0
    c2
    cuz
    cfv
    wcel
    #
    @11
    @12
    wa
    @7
    @13
    @8
    @0
    prmuz2
    adantr
    @0
    eluz2b2
    sylib
    #
    simpld
    #
    nnred
    #
    @9
    @0
    @1
    @16
    @8
    @1
    cn0
    wcel
    @7
    @1
    nnnn0
    adantl
    reexpcld
    @9
    @11
    @12
    @14
    simprd
    @9
    @0
    c1
    cexp
    co
    @0
    @2
    cle
    @9
    @0
    @9
    @0
    @15
    nncnd
    exp1d
    @9
    @0
    c1
    @1
    @16
    @9
    @0
    @15
    nnge1d
    @9
    @1
    cn
    c1
    cuz
    cfv
    @7
    @8
    simpr
    nnuz
    syl6eleq
    leexp2ad
    eqbrtrrd
    ltletrd
    ltned
    neneqd
    nrexdv
    nrex
    @5
    @6
    cc0
    c1
    cn
    wcel
    @6
    cc0
    wne
    @5
    wb
    1nn
    c1
    vk
    vp
    isppw2
    ax-mp
    necon1bbii
    mpbi
end
