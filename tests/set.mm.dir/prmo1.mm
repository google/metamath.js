include "c1.mm"
include "cprmo.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cprime.mm"
include "wcel.mm"
include "cif.mm"
include "cprod.mm"
include "cn0.mm"
include "wceq.mm"
include "1nn0.mm"
include "prmoval.mm"
include "ax-mp.mm"
include "cz.mm"
include "cc.mm"
include "wa.mm"
include "1z.mm"
include "ax-1cn.mm"
include "pm3.2i.mm"
include "wn.mm"
include "1nprm.mm"
include "a1i.mm"
include "eleq1.mm"
include "notbid.mm"
include "mpbird.mm"
include "iffalse.mm"
include "syl.mm"
include "fprod1.mm"
include "eqid.mm"
include "eqtri.mm"

theorem prmo1
  let vk: setvar k


  assert |- ( #p ` 1 ) = 1

  proof
    c1
    cprmo
    cfv
    #
    c1
    c1
    cfz
    co
    vk
    cv
    #
    cprime
    wcel
    #
    @1
    c1
    cif
    #
    vk
    cprod
    #
    c1
    c1
    cn0
    wcel
    @0
    @4
    wceq
    1nn0
    vk
    c1
    prmoval
    ax-mp
    @4
    c1
    c1
    @4
    c1
    c1
    c1
    cz
    wcel
    #
    c1
    cc
    wcel
    #
    wa
    @4
    c1
    wceq
    @5
    @6
    1z
    ax-1cn
    pm3.2i
    @3
    c1
    vk
    c1
    @1
    c1
    wceq
    #
    @2
    wn
    #
    @3
    c1
    wceq
    @7
    @8
    c1
    cprime
    wcel
    #
    wn
    #
    @10
    @7
    1nprm
    a1i
    @7
    @2
    @9
    @1
    c1
    cprime
    eleq1
    notbid
    mpbird
    @2
    @1
    c1
    iffalse
    syl
    fprod1
    ax-mp
    c1
    eqid
    #
    eqtri
    @11
    eqtri
    eqtri
end
