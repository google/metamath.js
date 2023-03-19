include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cdiv.mm"
include "csu.mm"
include "caddc.mm"
include "clog.mm"
include "cfv.mm"
include "cmin.mm"
include "cem.mm"
include "cicc.mm"
include "elnn0.mm"
include "c2.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "wss.mm"
include "0re.mm"
include "emre.mm"
include "ceu.mm"
include "2re.mm"
include "ere.mm"
include "clt.mm"
include "c3.mm"
include "egt2lt3.mm"
include "simpli.mm"
include "ltleii.mm"
include "crp.mm"
include "wb.mm"
include "2rp.mm"
include "epr.mm"
include "logleb.mm"
include "mp2an.mm"
include "mpbi.mm"
include "loge.mm"
include "breqtri.mm"
include "1re.mm"
include "relogcl.mm"
include "ax-mp.mm"
include "subge0i.mm"
include "mpbir.mm"
include "leidi.mm"
include "iccss.mm"
include "mp4an.mm"
include "harmonicbnd2.mm"
include "sseldi.mm"
include "c0.mm"
include "oveq2.mm"
include "fz10.mm"
include "syl6eq.mm"
include "sumeq1d.mm"
include "sum0.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "fveq2d.mm"
include "log1.mm"
include "oveq12d.mm"
include "0m0e0.mm"
include "emgt0.mm"
include "elicc2i.mm"
include "mpbir3an.mm"
include "syl6eqel.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem harmonicbnd3
  let vm: setvar m
  let cN: class N
  let cA: class A

  disjoint N m
  disjoint A m
  assert |- ( N e. NN0 -> ( sum_ m e. ( 1 ... N ) ( 1 / m ) - ( log ` ( N + 1 ) ) ) e. ( 0 [,] gamma ) )

  proof
    cN
    cn0
    wcel
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    c1
    cN
    cfz
    co
    #
    c1
    vm
    cv
    cdiv
    co
    #
    vm
    csu
    #
    cN
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cc0
    cem
    cicc
    co
    #
    wcel
    #
    cN
    elnn0
    @0
    @9
    @1
    @0
    c1
    c2
    clog
    cfv
    #
    cmin
    co
    #
    cem
    cicc
    co
    #
    @8
    @7
    cc0
    cr
    wcel
    #
    cem
    cr
    wcel
    cc0
    @11
    cle
    wbr
    #
    cem
    cem
    cle
    wbr
    @12
    @8
    wss
    0re
    emre
    @14
    @10
    c1
    cle
    wbr
    @10
    ceu
    clog
    cfv
    #
    c1
    cle
    c2
    ceu
    cle
    wbr
    #
    @10
    @15
    cle
    wbr
    #
    c2
    ceu
    2re
    ere
    c2
    ceu
    clt
    wbr
    ceu
    c3
    clt
    wbr
    egt2lt3
    simpli
    ltleii
    c2
    crp
    wcel
    #
    ceu
    crp
    wcel
    @16
    @17
    wb
    2rp
    epr
    c2
    ceu
    logleb
    mp2an
    mpbi
    loge
    breqtri
    c1
    @10
    1re
    @18
    @10
    cr
    wcel
    2rp
    c2
    relogcl
    ax-mp
    subge0i
    mpbir
    cem
    emre
    leidi
    cc0
    cem
    @11
    cem
    iccss
    mp4an
    vm
    cN
    harmonicbnd2
    sseldi
    @1
    @7
    cc0
    @8
    @1
    @7
    cc0
    cc0
    cmin
    co
    cc0
    @1
    @4
    cc0
    @6
    cc0
    cmin
    @1
    @4
    c0
    @3
    vm
    csu
    cc0
    @1
    @2
    c0
    @3
    vm
    @1
    @2
    c1
    cc0
    cfz
    co
    c0
    cN
    cc0
    c1
    cfz
    oveq2
    fz10
    syl6eq
    sumeq1d
    @3
    vm
    sum0
    syl6eq
    @1
    @6
    c1
    clog
    cfv
    cc0
    @1
    @5
    c1
    clog
    @1
    @5
    cc0
    c1
    caddc
    co
    c1
    cN
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    fveq2d
    log1
    syl6eq
    oveq12d
    0m0e0
    syl6eq
    cc0
    @8
    wcel
    @13
    cc0
    cc0
    cle
    wbr
    cc0
    cem
    cle
    wbr
    0re
    cc0
    0re
    leidi
    cc0
    cem
    0re
    emre
    emgt0
    ltleii
    cc0
    cem
    cc0
    0re
    emre
    elicc2i
    mpbir3an
    syl6eqel
    jaoi
    sylbi
end
