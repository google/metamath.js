include "cn.mm"
include "cr.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "cli.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cabs.mm"
include "c1.mm"
include "clt.mm"
include "cuz.mm"
include "wral.mm"
include "csin.mm"
include "cdiv.mm"
include "co.mm"
include "cmpt.mm"
include "ccom.mm"
include "nnuz.mm"
include "1zzd.mm"
include "crp.mm"
include "wcel.mm"
include "1rp.mm"
include "a1i.mm"
include "eqidd.mm"
include "simpr.mm"
include "climi0.mm"
include "cc.mm"
include "c2.mm"
include "cexp.mm"
include "c3.mm"
include "cmin.mm"
include "simpll.mm"
include "simplr.mm"
include "eqid.mm"
include "simprl.mm"
include "simprr.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "sinccvglem.mm"
include "rexlimddv.mm"

theorem sinccvg
  let vx: setvar x
  let cF: class F
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n

  disjoint F x
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint F j
  disjoint k n
  disjoint k x
  disjoint F k
  disjoint n x
  disjoint F n
  assert |- ( ( F : NN --> ( RR \ { 0 } ) /\ F ~~> 0 ) -> ( ( x e. ( RR \ { 0 } ) |-> ( ( sin ` x ) / x ) ) o. F ) ~~> 1 )

  proof
    cn
    cr
    cc0
    csn
    cdif
    #
    cF
    wf
    #
    cF
    cc0
    cli
    wbr
    #
    wa
    #
    vk
    cv
    #
    cF
    cfv
    #
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vx
    @0
    vx
    cv
    #
    csin
    cfv
    @11
    cdiv
    co
    cmpt
    #
    cF
    ccom
    c1
    cli
    wbr
    vj
    cn
    @3
    @5
    c1
    vj
    vk
    cF
    c1
    cn
    nnuz
    @3
    1zzd
    c1
    crp
    wcel
    @3
    1rp
    a1i
    @3
    @4
    cn
    wcel
    wa
    @5
    eqidd
    @1
    @2
    simpr
    climi0
    @3
    @8
    cn
    wcel
    #
    @10
    wa
    #
    wa
    #
    vx
    vn
    cF
    @12
    vx
    cc
    c1
    @11
    c2
    cexp
    co
    c3
    cdiv
    co
    cmin
    co
    cmpt
    #
    @8
    @1
    @2
    @14
    simpll
    @1
    @2
    @14
    simplr
    @12
    eqid
    @16
    eqid
    @3
    @13
    @10
    simprl
    @15
    @10
    vn
    cv
    #
    @9
    wcel
    @17
    cF
    cfv
    #
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    @3
    @13
    @10
    simprr
    @7
    @20
    vk
    @17
    @9
    vk
    vn
    weq
    #
    @6
    @19
    c1
    clt
    @21
    @5
    @18
    cabs
    @4
    @17
    cF
    fveq2
    fveq2d
    breq1d
    rspccva
    sylan
    sinccvglem
    rexlimddv
end
