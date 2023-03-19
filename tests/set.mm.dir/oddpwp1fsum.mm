include "c1.mm"
include "cneg.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "caddc.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "csu.mm"
include "c2.mm"
include "cdvds.mm"
include "wbr.mm"
include "wceq.mm"
include "wn.mm"
include "cz.mm"
include "wcel.mm"
include "wb.mm"
include "nnzd.mm"
include "oddm1even.mm"
include "syl.mm"
include "mpbid.mm"
include "m1expe.mm"
include "oveq1d.mm"
include "pwp1fsum.mm"
include "nnnn0d.mm"
include "expcld.mm"
include "mulid2d.mm"
include "3eqtr3rd.mm"

theorem oddpwp1fsum
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cN: class N
  let vl: setvar l
  assume pwp1fsum.a: |- ( ph -> A e. CC )
  assume pwp1fsum.n: |- ( ph -> N e. NN )
  assume oddpwp1fsum.n: |- ( ph -> -. 2 || N )

  disjoint A k
  disjoint N k
  disjoint k ph
  disjoint A l
  disjoint k l
  disjoint N l
  disjoint l ph
  assert |- ( ph -> ( ( A ^ N ) + 1 ) = ( ( A + 1 ) x. sum_ k e. ( 0 ... ( N - 1 ) ) ( ( -u 1 ^ k ) x. ( A ^ k ) ) ) )

  proof
    wph
    c1
    cneg
    #
    cN
    c1
    cmin
    co
    #
    cexp
    co
    #
    cA
    cN
    cexp
    co
    #
    cmul
    co
    #
    c1
    caddc
    co
    c1
    @3
    cmul
    co
    #
    c1
    caddc
    co
    cA
    c1
    caddc
    co
    cc0
    @1
    cfz
    co
    @0
    vk
    cv
    #
    cexp
    co
    cA
    @6
    cexp
    co
    cmul
    co
    vk
    csu
    cmul
    co
    @3
    c1
    caddc
    co
    wph
    @4
    @5
    c1
    caddc
    wph
    @2
    c1
    @3
    cmul
    wph
    c2
    @1
    cdvds
    wbr
    #
    @2
    c1
    wceq
    wph
    c2
    cN
    cdvds
    wbr
    wn
    #
    @7
    oddpwp1fsum.n
    wph
    cN
    cz
    wcel
    @8
    @7
    wb
    wph
    cN
    pwp1fsum.n
    nnzd
    cN
    oddm1even
    syl
    mpbid
    @1
    m1expe
    syl
    oveq1d
    oveq1d
    wph
    cA
    vk
    cN
    pwp1fsum.a
    pwp1fsum.n
    pwp1fsum
    wph
    @5
    @3
    c1
    caddc
    wph
    @3
    wph
    cA
    cN
    pwp1fsum.a
    wph
    cN
    pwp1fsum.n
    nnnn0d
    expcld
    mulid2d
    oveq1d
    3eqtr3rd
end
