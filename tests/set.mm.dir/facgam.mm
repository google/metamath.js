include "cv.mm"
include "cfa.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cgam.mm"
include "wceq.mm"
include "cc0.mm"
include "fveq2.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "gam1.mm"
include "eqeq12d.mm"
include "fac0.mm"
include "cn0.mm"
include "wcel.mm"
include "cmul.mm"
include "facp1.mm"
include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "nn0p1nn.mm"
include "nncnd.mm"
include "eldifn.mm"
include "nsyl3.mm"
include "eldifd.mm"
include "gamp1.mm"
include "syl.mm"
include "syl5ibr.mm"
include "nn0ind.mm"

theorem facgam
  let cN: class N
  let vn: setvar n
  let vx: setvar x


  assert |- ( N e. NN0 -> ( ! ` N ) = ( _G ` ( N + 1 ) ) )

  proof
    vx
    cv
    #
    cfa
    cfv
    #
    @0
    c1
    caddc
    co
    #
    cgam
    cfv
    #
    wceq
    cc0
    cfa
    cfv
    #
    c1
    wceq
    vn
    cv
    #
    cfa
    cfv
    #
    @5
    c1
    caddc
    co
    #
    cgam
    cfv
    #
    wceq
    #
    @7
    cfa
    cfv
    #
    @7
    c1
    caddc
    co
    #
    cgam
    cfv
    #
    wceq
    #
    cN
    cfa
    cfv
    #
    cN
    c1
    caddc
    co
    #
    cgam
    cfv
    #
    wceq
    vx
    vn
    cN
    @0
    cc0
    wceq
    #
    @1
    @4
    @3
    c1
    @0
    cc0
    cfa
    fveq2
    @17
    @3
    c1
    cgam
    cfv
    c1
    @17
    @2
    c1
    cgam
    @17
    @2
    cc0
    c1
    caddc
    co
    c1
    @0
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    fveq2d
    gam1
    syl6eq
    eqeq12d
    @0
    @5
    wceq
    #
    @1
    @6
    @3
    @8
    @0
    @5
    cfa
    fveq2
    @18
    @2
    @7
    cgam
    @0
    @5
    c1
    caddc
    oveq1
    fveq2d
    eqeq12d
    @0
    @7
    wceq
    #
    @1
    @10
    @3
    @12
    @0
    @7
    cfa
    fveq2
    @19
    @2
    @11
    cgam
    @0
    @7
    c1
    caddc
    oveq1
    fveq2d
    eqeq12d
    @0
    cN
    wceq
    #
    @1
    @14
    @3
    @16
    @0
    cN
    cfa
    fveq2
    @20
    @2
    @15
    cgam
    @0
    cN
    c1
    caddc
    oveq1
    fveq2d
    eqeq12d
    fac0
    @9
    @13
    @5
    cn0
    wcel
    #
    @6
    @7
    cmul
    co
    #
    @8
    @7
    cmul
    co
    #
    wceq
    @6
    @8
    @7
    cmul
    oveq1
    @21
    @10
    @22
    @12
    @23
    @5
    facp1
    @21
    @7
    cc
    cz
    cn
    cdif
    #
    cdif
    wcel
    @12
    @23
    wceq
    @21
    @7
    cc
    @24
    @21
    @7
    @5
    nn0p1nn
    #
    nncnd
    @7
    @24
    wcel
    @7
    cn
    wcel
    @21
    @7
    cz
    cn
    eldifn
    @25
    nsyl3
    eldifd
    @7
    gamp1
    syl
    eqeq12d
    syl5ibr
    nn0ind
end
