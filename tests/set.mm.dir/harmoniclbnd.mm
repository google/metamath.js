include "crp.mm"
include "wcel.mm"
include "clog.mm"
include "cfv.mm"
include "cfl.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "cdiv.mm"
include "csu.mm"
include "relogcl.mm"
include "cr.mm"
include "cn0.mm"
include "cn.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "rprege0.mm"
include "flge0nn0.mm"
include "syl.mm"
include "nn0p1nn.mm"
include "nnrpd.mm"
include "fzfid.mm"
include "elfznn.mm"
include "adantl.mm"
include "nnrecred.mm"
include "fsumrecl.mm"
include "rpre.mm"
include "fllep1.mm"
include "id.mm"
include "logled.mm"
include "mpbid.mm"
include "cmin.mm"
include "cem.mm"
include "cicc.mm"
include "harmonicbnd3.mm"
include "0re.mm"
include "emre.mm"
include "elicc2i.mm"
include "simp2bi.mm"
include "subge0d.mm"
include "letrd.mm"

theorem harmoniclbnd
  let cA: class A
  let vm: setvar m
  let cN: class N

  disjoint A m
  disjoint N m
  assert |- ( A e. RR+ -> ( log ` A ) <_ sum_ m e. ( 1 ... ( |_ ` A ) ) ( 1 / m ) )

  proof
    cA
    crp
    wcel
    #
    cA
    clog
    cfv
    #
    cA
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    clog
    cfv
    #
    c1
    @2
    cfz
    co
    #
    c1
    vm
    cv
    #
    cdiv
    co
    #
    vm
    csu
    #
    cA
    relogcl
    @0
    @3
    crp
    wcel
    @4
    cr
    wcel
    @0
    @3
    @0
    @2
    cn0
    wcel
    #
    @3
    cn
    wcel
    @0
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    wa
    @9
    cA
    rprege0
    cA
    flge0nn0
    syl
    #
    @2
    nn0p1nn
    syl
    nnrpd
    #
    @3
    relogcl
    syl
    #
    @0
    @5
    @7
    vm
    @0
    c1
    @2
    fzfid
    @0
    @6
    @5
    wcel
    #
    wa
    @6
    @14
    @6
    cn
    wcel
    @0
    @6
    @2
    elfznn
    adantl
    nnrecred
    fsumrecl
    #
    @0
    cA
    @3
    cle
    wbr
    #
    @1
    @4
    cle
    wbr
    @0
    @10
    @16
    cA
    rpre
    cA
    fllep1
    syl
    @0
    cA
    @3
    @0
    id
    @12
    logled
    mpbid
    @0
    cc0
    @8
    @4
    cmin
    co
    #
    cle
    wbr
    #
    @4
    @8
    cle
    wbr
    @0
    @17
    cc0
    cem
    cicc
    co
    wcel
    #
    @18
    @0
    @9
    @19
    @11
    vm
    @2
    harmonicbnd3
    syl
    @19
    @17
    cr
    wcel
    @18
    @17
    cem
    cle
    wbr
    cc0
    cem
    @17
    0re
    emre
    elicc2i
    simp2bi
    syl
    @0
    @8
    @4
    @15
    @13
    subge0d
    mpbid
    letrd
end
