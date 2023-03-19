include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfmtno.mm"
include "cfv.mm"
include "cc0.mm"
include "cfz.mm"
include "cprod.mm"
include "c2.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "prodeq1d.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "weq.mm"
include "prodeq1.mm"
include "syl.mm"
include "c5.mm"
include "c3.mm"
include "fmtno0.mm"
include "oveq1i.mm"
include "3p2e5.mm"
include "eqtri.mm"
include "csn.mm"
include "fz0sn.mm"
include "prodeq1i.mm"
include "cz.mm"
include "wcel.mm"
include "cc.mm"
include "0z.mm"
include "cn0.mm"
include "0nn0.mm"
include "fmtnonn.mm"
include "nncnd.mm"
include "ax-mp.mm"
include "fveq2.mm"
include "prodsn.mm"
include "mp2an.mm"
include "0p1e1.mm"
include "fveq2i.mm"
include "fmtno1.mm"
include "3eqtr4ri.mm"
include "fmtnorec2lem.mm"
include "nn0ind.mm"

theorem fmtnorec2
  let vn: setvar n
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k

  disjoint N n
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint N x
  disjoint k x
  assert |- ( N e. NN0 -> ( FermatNo ` ( N + 1 ) ) = ( prod_ n e. ( 0 ... N ) ( FermatNo ` n ) + 2 ) )

  proof
    vx
    cv
    #
    c1
    caddc
    co
    #
    cfmtno
    cfv
    #
    cc0
    @0
    cfz
    co
    #
    vn
    cv
    #
    cfmtno
    cfv
    #
    vn
    cprod
    #
    c2
    caddc
    co
    #
    wceq
    cc0
    c1
    caddc
    co
    #
    cfmtno
    cfv
    #
    cc0
    cc0
    cfz
    co
    #
    @5
    vn
    cprod
    #
    c2
    caddc
    co
    #
    wceq
    vy
    cv
    #
    c1
    caddc
    co
    #
    cfmtno
    cfv
    #
    cc0
    @13
    cfz
    co
    #
    @5
    vn
    cprod
    #
    c2
    caddc
    co
    #
    wceq
    @14
    c1
    caddc
    co
    #
    cfmtno
    cfv
    #
    cc0
    @14
    cfz
    co
    #
    @5
    vn
    cprod
    #
    c2
    caddc
    co
    #
    wceq
    cN
    c1
    caddc
    co
    #
    cfmtno
    cfv
    #
    cc0
    cN
    cfz
    co
    #
    @5
    vn
    cprod
    #
    c2
    caddc
    co
    #
    wceq
    vx
    vy
    cN
    @0
    cc0
    wceq
    #
    @2
    @9
    @7
    @12
    @29
    @1
    @8
    cfmtno
    @0
    cc0
    c1
    caddc
    oveq1
    fveq2d
    @29
    @6
    @11
    c2
    caddc
    @29
    @3
    @10
    @5
    vn
    @0
    cc0
    cc0
    cfz
    oveq2
    prodeq1d
    oveq1d
    eqeq12d
    vx
    vy
    weq
    #
    @2
    @15
    @7
    @18
    @30
    @1
    @14
    cfmtno
    @0
    @13
    c1
    caddc
    oveq1
    fveq2d
    @30
    @6
    @17
    c2
    caddc
    @30
    @3
    @16
    @5
    vn
    @0
    @13
    cc0
    cfz
    oveq2
    prodeq1d
    oveq1d
    eqeq12d
    @0
    @14
    wceq
    #
    @2
    @20
    @7
    @23
    @31
    @1
    @19
    cfmtno
    @0
    @14
    c1
    caddc
    oveq1
    fveq2d
    @31
    @6
    @22
    c2
    caddc
    @31
    @3
    @21
    @5
    vn
    @0
    @14
    cc0
    cfz
    oveq2
    prodeq1d
    oveq1d
    eqeq12d
    @0
    cN
    wceq
    #
    @2
    @25
    @7
    @28
    @32
    @1
    @24
    cfmtno
    @0
    cN
    c1
    caddc
    oveq1
    fveq2d
    @32
    @3
    @26
    wceq
    #
    @7
    @28
    wceq
    @0
    cN
    cc0
    cfz
    oveq2
    @33
    @6
    @27
    c2
    caddc
    @3
    @26
    @5
    vn
    prodeq1
    oveq1d
    syl
    eqeq12d
    cc0
    cfmtno
    cfv
    #
    c2
    caddc
    co
    #
    c5
    @12
    @9
    @35
    c3
    c2
    caddc
    co
    c5
    @34
    c3
    c2
    caddc
    fmtno0
    oveq1i
    3p2e5
    eqtri
    @11
    @34
    c2
    caddc
    @11
    cc0
    csn
    #
    @5
    vn
    cprod
    #
    @34
    @10
    @36
    @5
    vn
    fz0sn
    prodeq1i
    cc0
    cz
    wcel
    @34
    cc
    wcel
    #
    @37
    @34
    wceq
    0z
    cc0
    cn0
    wcel
    #
    @38
    0nn0
    @39
    @34
    cc0
    fmtnonn
    nncnd
    ax-mp
    @5
    @34
    vn
    cc0
    cz
    @4
    cc0
    cfmtno
    fveq2
    prodsn
    mp2an
    eqtri
    oveq1i
    @9
    c1
    cfmtno
    cfv
    c5
    @8
    c1
    cfmtno
    0p1e1
    fveq2i
    fmtno1
    eqtri
    3eqtr4ri
    vy
    vn
    fmtnorec2lem
    nn0ind
end
