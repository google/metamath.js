include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cvdwa.mm"
include "cfv.mm"
include "co.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "wrex.mm"
include "wn.mm"
include "c0.mm"
include "noel.mm"
include "pm2.21i.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "0re.mm"
include "ltm1.mm"
include "ax-mp.mm"
include "cz.mm"
include "wb.mm"
include "0z.mm"
include "peano2zm.mm"
include "fzn.mm"
include "mp2an.mm"
include "mpbi.mm"
include "eleq2s.mm"
include "nrex.mm"
include "cn0.mm"
include "0nn0.mm"
include "vdwapval.mm"
include "mp3an1.mm"
include "mtbiri.mm"
include "eq0rdv.mm"

theorem vdwap0
  let cA: class A
  let cD: class D
  let va: setvar a
  let vd: setvar d
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vk: setvar k
  let cK: class K
  let cX: class X


  assert |- ( ( A e. NN /\ D e. NN ) -> ( A ( AP ` 0 ) D ) = (/) )

  proof
    cA
    cn
    wcel
    #
    cD
    cn
    wcel
    #
    wa
    #
    vx
    cA
    cD
    cc0
    cvdwa
    cfv
    co
    #
    @2
    vx
    cv
    #
    @3
    wcel
    #
    @4
    cA
    vm
    cv
    #
    cD
    cmul
    co
    caddc
    co
    wceq
    #
    vm
    cc0
    cc0
    c1
    cmin
    co
    #
    cfz
    co
    #
    wrex
    #
    @7
    vm
    @9
    @7
    wn
    #
    @6
    c0
    @9
    @6
    c0
    wcel
    @11
    @6
    noel
    pm2.21i
    @8
    cc0
    clt
    wbr
    #
    @9
    c0
    wceq
    #
    cc0
    cr
    wcel
    @12
    0re
    cc0
    ltm1
    ax-mp
    cc0
    cz
    wcel
    #
    @8
    cz
    wcel
    #
    @12
    @13
    wb
    0z
    @14
    @15
    0z
    cc0
    peano2zm
    ax-mp
    cc0
    @8
    fzn
    mp2an
    mpbi
    eleq2s
    nrex
    cc0
    cn0
    wcel
    @0
    @1
    @5
    @10
    wb
    0nn0
    cA
    cD
    vm
    cc0
    @4
    vdwapval
    mp3an1
    mtbiri
    eq0rdv
end
