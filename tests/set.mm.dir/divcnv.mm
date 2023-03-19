include "cc.mm"
include "wcel.mm"
include "cn.mm"
include "cv.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "cc0.mm"
include "crli.mm"
include "wbr.mm"
include "cli.mm"
include "crp.mm"
include "wss.mm"
include "nnrp.mm"
include "ssriv.mm"
include "a1i.mm"
include "divrcnv.mm"
include "rlimres2.mm"
include "c1.mm"
include "nnuz.mm"
include "1zzd.mm"
include "wa.mm"
include "simpl.mm"
include "nncn.mm"
include "adantl.mm"
include "wne.mm"
include "nnne0.mm"
include "divcld.mm"
include "eqid.mm"
include "fmptd.mm"
include "rlimclim.mm"
include "mpbid.mm"

theorem divcnv
  let cA: class A
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y

  disjoint A n
  disjoint n x
  disjoint n y
  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( A e. CC -> ( n e. NN |-> ( A / n ) ) ~~> 0 )

  proof
    cA
    cc
    wcel
    #
    vn
    cn
    cA
    vn
    cv
    #
    cdiv
    co
    #
    cmpt
    #
    cc0
    crli
    wbr
    @3
    cc0
    cli
    wbr
    @0
    vn
    cn
    crp
    @2
    cc0
    cn
    crp
    wss
    @0
    vn
    cn
    crp
    @1
    nnrp
    ssriv
    a1i
    cA
    vn
    divrcnv
    rlimres2
    @0
    cc0
    @3
    c1
    cn
    nnuz
    @0
    1zzd
    @0
    vn
    cn
    @2
    cc
    @3
    @0
    @1
    cn
    wcel
    #
    wa
    cA
    @1
    @0
    @4
    simpl
    @4
    @1
    cc
    wcel
    @0
    @1
    nncn
    adantl
    @4
    @1
    cc0
    wne
    @0
    @1
    nnne0
    adantl
    divcld
    @3
    eqid
    fmptd
    rlimclim
    mpbid
end
