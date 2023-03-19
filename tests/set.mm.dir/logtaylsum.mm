include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cmin.mm"
include "clog.mm"
include "cneg.mm"
include "cn.mm"
include "cmpt.mm"
include "nnuz.mm"
include "1zzd.mm"
include "wceq.mm"
include "oveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "cn0.mm"
include "simpl.mm"
include "nnnn0.mm"
include "expcl.mm"
include "syl2an.mm"
include "nncn.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0.mm"
include "divcld.mm"
include "logtayl.mm"
include "isumclim.mm"

theorem logtaylsum
  let cA: class A
  let vk: setvar k
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cS: class S

  disjoint A k
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j r
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint A j
  disjoint k m
  disjoint k n
  disjoint k r
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m r
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n r
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint S n
  assert |- ( ( A e. CC /\ ( abs ` A ) < 1 ) -> sum_ k e. NN ( ( A ^ k ) / k ) = -u ( log ` ( 1 - A ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cabs
    cfv
    c1
    clt
    wbr
    #
    wa
    #
    cA
    vk
    cv
    #
    cexp
    co
    #
    @3
    cdiv
    co
    #
    c1
    cA
    cmin
    co
    clog
    cfv
    cneg
    vk
    vn
    cn
    cA
    vn
    cv
    #
    cexp
    co
    #
    @6
    cdiv
    co
    #
    cmpt
    #
    c1
    cn
    nnuz
    @2
    1zzd
    @3
    cn
    wcel
    #
    @3
    @9
    cfv
    @5
    wceq
    @2
    vn
    @3
    @8
    @5
    cn
    @9
    @6
    @3
    wceq
    #
    @7
    @4
    @6
    @3
    cdiv
    @6
    @3
    cA
    cexp
    oveq2
    @11
    id
    oveq12d
    @9
    eqid
    @4
    @3
    cdiv
    ovex
    fvmpt
    adantl
    @2
    @10
    wa
    @4
    @3
    @2
    @0
    @3
    cn0
    wcel
    @4
    cc
    wcel
    @10
    @0
    @1
    simpl
    @3
    nnnn0
    cA
    @3
    expcl
    syl2an
    @10
    @3
    cc
    wcel
    @2
    @3
    nncn
    adantl
    @10
    @3
    cc0
    wne
    @2
    @3
    nnne0
    adantl
    divcld
    cA
    vn
    logtayl
    isumclim
end
