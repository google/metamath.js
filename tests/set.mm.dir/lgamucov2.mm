include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "cnt.mm"
include "wcel.mm"
include "cn.mm"
include "wrex.mm"
include "eqid.mm"
include "lgamucov.mm"
include "ctop.mm"
include "cc.mm"
include "wss.mm"
include "cnfldtop.mm"
include "cv.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cn0.mm"
include "wral.mm"
include "wa.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "ntrss2.mm"
include "mp2an.mm"
include "sseli.mm"
include "reximi.mm"
include "syl.mm"

theorem lgamucov2
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cU: class U
  let vk: setvar k
  let vr: setvar r
  let va: setvar a
  let vm: setvar m
  let vn: setvar n
  let vt: setvar t
  let vz: setvar z
  let cG: class G
  let cJ: class J
  assume lgamucov.u: |- U = { x e. CC | ( ( abs ` x ) <_ r /\ A. k e. NN0 ( 1 / r ) <_ ( abs ` ( x + k ) ) ) }
  assume lgamucov.a: |- ( ph -> A e. ( CC \ ( ZZ \ NN ) ) )

  disjoint k r
  disjoint k x
  disjoint A k
  disjoint r x
  disjoint A r
  disjoint A x
  disjoint k ph
  disjoint ph r
  disjoint ph x
  disjoint a k
  disjoint a m
  disjoint a n
  disjoint a r
  disjoint a t
  disjoint a x
  disjoint a z
  disjoint A a
  disjoint k m
  disjoint k n
  disjoint k t
  disjoint k z
  disjoint m n
  disjoint m r
  disjoint m t
  disjoint m x
  disjoint m z
  disjoint A m
  disjoint n r
  disjoint n t
  disjoint n x
  disjoint n z
  disjoint A n
  disjoint r t
  disjoint r z
  disjoint t x
  disjoint t z
  disjoint A t
  disjoint x z
  disjoint A z
  disjoint G n
  disjoint G r
  disjoint G z
  disjoint J a
  disjoint a ph
  disjoint m ph
  disjoint n ph
  disjoint ph t
  disjoint ph z
  disjoint U a
  disjoint U m
  disjoint U n
  disjoint U t
  disjoint U z
  assert |- ( ph -> E. r e. NN A e. U )

  proof
    wph
    cA
    cU
    ccnfld
    ctopn
    cfv
    #
    cnt
    cfv
    cfv
    #
    wcel
    #
    vr
    cn
    wrex
    cA
    cU
    wcel
    #
    vr
    cn
    wrex
    wph
    vx
    cA
    cU
    vk
    @0
    vr
    lgamucov.u
    lgamucov.a
    @0
    eqid
    #
    lgamucov
    @2
    @3
    vr
    cn
    @1
    cU
    cA
    @0
    ctop
    wcel
    cU
    cc
    wss
    @1
    cU
    wss
    @0
    @4
    cnfldtop
    cU
    vx
    cv
    #
    cabs
    cfv
    vr
    cv
    #
    cle
    wbr
    c1
    @6
    cdiv
    co
    @5
    vk
    cv
    caddc
    co
    cabs
    cfv
    cle
    wbr
    vk
    cn0
    wral
    wa
    #
    vx
    cc
    crab
    cc
    lgamucov.u
    @7
    vx
    cc
    ssrab2
    eqsstri
    cU
    @0
    cc
    cc
    @0
    @0
    @4
    cnfldtopon
    toponunii
    ntrss2
    mp2an
    sseli
    reximi
    syl
end
