include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfmtno.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "cmin.mm"
include "wceq.mm"
include "peano2nn0.mm"
include "fmtno.mm"
include "syl.mm"
include "cmul.mm"
include "cc.mm"
include "2nn0.mm"
include "nn0expcl.mm"
include "mpan.mm"
include "wa.mm"
include "nn0cnd.mm"
include "sylancr.mm"
include "pncan1.mm"
include "oveq1d.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "2cnne0.mm"
include "nn0zd.mm"
include "2z.mm"
include "jctir.mm"
include "expmulz.mm"
include "2cn.mm"
include "2ne0.mm"
include "nn0z.mm"
include "expp1z.mm"
include "mp3an12i.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "3eqtr2rd.mm"
include "3eqtrd.mm"

theorem fmtnorec1
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN0 -> ( FermatNo ` ( N + 1 ) ) = ( ( ( ( FermatNo ` N ) - 1 ) ^ 2 ) + 1 ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    c1
    caddc
    co
    #
    cfmtno
    cfv
    #
    c2
    c2
    @1
    cexp
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    #
    c2
    c2
    cN
    cexp
    co
    #
    cexp
    co
    #
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    c2
    cexp
    co
    #
    c1
    caddc
    co
    cN
    cfmtno
    cfv
    #
    c1
    cmin
    co
    #
    c2
    cexp
    co
    #
    c1
    caddc
    co
    @0
    @1
    cn0
    wcel
    @2
    @5
    wceq
    cN
    peano2nn0
    @1
    fmtno
    syl
    @0
    @4
    @10
    c1
    caddc
    @0
    @10
    @7
    c2
    cexp
    co
    #
    c2
    @6
    c2
    cmul
    co
    #
    cexp
    co
    #
    @4
    @0
    @9
    @7
    c2
    cexp
    @0
    @7
    cc
    wcel
    #
    @9
    @7
    wceq
    @0
    c2
    cn0
    wcel
    #
    @6
    cn0
    wcel
    #
    @17
    2nn0
    @18
    @0
    @19
    2nn0
    c2
    cN
    nn0expcl
    mpan
    #
    @18
    @19
    wa
    @7
    c2
    @6
    nn0expcl
    nn0cnd
    sylancr
    @7
    pncan1
    syl
    oveq1d
    @0
    c2
    cc
    wcel
    #
    c2
    cc0
    wne
    #
    wa
    @6
    cz
    wcel
    #
    c2
    cz
    wcel
    #
    wa
    @16
    @14
    wceq
    2cnne0
    @0
    @23
    @24
    @0
    @6
    @20
    nn0zd
    2z
    jctir
    c2
    @6
    c2
    expmulz
    sylancr
    @0
    @15
    @3
    c2
    cexp
    @0
    @3
    @15
    @21
    @22
    @0
    cN
    cz
    wcel
    @3
    @15
    wceq
    2cn
    2ne0
    cN
    nn0z
    c2
    cN
    expp1z
    mp3an12i
    eqcomd
    oveq2d
    3eqtr2rd
    oveq1d
    @0
    @10
    @13
    c1
    caddc
    @0
    @9
    @12
    c2
    cexp
    @0
    @8
    @11
    c1
    cmin
    @0
    @11
    @8
    cN
    fmtno
    eqcomd
    oveq1d
    oveq1d
    oveq1d
    3eqtrd
end
