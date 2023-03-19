include "cv.mm"
include "cabs.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cn0.mm"
include "wral.mm"
include "wa.mm"
include "cc.mm"
include "crab.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "wcel.mm"
include "w3a.mm"
include "cneg.mm"
include "wn.mm"
include "simp2.mm"
include "cc0.mm"
include "clt.mm"
include "3ad2ant1.mm"
include "nnred.mm"
include "nngt0d.mm"
include "recgt0d.mm"
include "0red.mm"
include "nnrecred.mm"
include "ltnled.mm"
include "mpbid.mm"
include "wi.mm"
include "wceq.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "rspccv.mm"
include "adantl.mm"
include "3ad2ant3.mm"
include "negidd.mm"
include "abs0.mm"
include "syl6eq.mm"
include "sylibd.mm"
include "mtod.mm"
include "eldmgm.mm"
include "sylanbrc.mm"
include "rabssdv.mm"
include "syl5eqss.mm"

theorem lgamgulmlem1
  let wph: wff ph
  let vx: setvar x
  let cR: class R
  let cU: class U
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vy: setvar y
  let cG: class G
  let vt: setvar t
  let cN: class N
  let vm: setvar m
  let vz: setvar z
  let cA: class A
  let cO: class O
  let cT: class T
  assume lgamgulm.r: |- ( ph -> R e. NN )
  assume lgamgulm.u: |- U = { x e. CC | ( ( abs ` x ) <_ R /\ A. k e. NN0 ( 1 / R ) <_ ( abs ` ( x + k ) ) ) }

  disjoint k x
  disjoint R k
  disjoint R x
  disjoint ph x
  disjoint n r
  disjoint n y
  disjoint G n
  disjoint r y
  disjoint G r
  disjoint G y
  disjoint t x
  disjoint t y
  disjoint N t
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint k m
  disjoint k n
  disjoint k r
  disjoint k t
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m r
  disjoint m t
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint R m
  disjoint n t
  disjoint n x
  disjoint n z
  disjoint R n
  disjoint r t
  disjoint r x
  disjoint r z
  disjoint R r
  disjoint t z
  disjoint R t
  disjoint x z
  disjoint y z
  disjoint R y
  disjoint R z
  disjoint U m
  disjoint U n
  disjoint U r
  disjoint U t
  disjoint U y
  disjoint U z
  disjoint A k
  disjoint A m
  disjoint A t
  disjoint A x
  disjoint A y
  disjoint O n
  disjoint O r
  disjoint O y
  disjoint m ph
  disjoint n ph
  disjoint ph r
  disjoint ph t
  disjoint ph y
  disjoint ph z
  disjoint T n
  disjoint T r
  disjoint T y
  assert |- ( ph -> U C_ ( CC \ ( ZZ \ NN ) ) )

  proof
    wph
    cU
    vx
    cv
    #
    cabs
    cfv
    cR
    cle
    wbr
    #
    c1
    cR
    cdiv
    co
    #
    @0
    vk
    cv
    #
    caddc
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    vk
    cn0
    wral
    #
    wa
    #
    vx
    cc
    crab
    cc
    cz
    cn
    cdif
    cdif
    #
    lgamgulm.u
    wph
    @8
    vx
    cc
    @9
    wph
    @0
    cc
    wcel
    #
    @8
    w3a
    #
    @10
    @0
    cneg
    #
    cn0
    wcel
    #
    wn
    @0
    @9
    wcel
    wph
    @10
    @8
    simp2
    #
    @11
    @13
    @2
    cc0
    cle
    wbr
    #
    @11
    cc0
    @2
    clt
    wbr
    @15
    wn
    @11
    cR
    @11
    cR
    wph
    @10
    cR
    cn
    wcel
    @8
    lgamgulm.r
    3ad2ant1
    #
    nnred
    @11
    cR
    @16
    nngt0d
    recgt0d
    @11
    cc0
    @2
    @11
    0red
    @11
    cR
    @16
    nnrecred
    ltnled
    mpbid
    @11
    @13
    @2
    @0
    @12
    caddc
    co
    #
    cabs
    cfv
    #
    cle
    wbr
    #
    @15
    @8
    wph
    @13
    @19
    wi
    #
    @10
    @7
    @20
    @1
    @6
    @19
    vk
    @12
    cn0
    @3
    @12
    wceq
    #
    @5
    @18
    @2
    cle
    @21
    @4
    @17
    cabs
    @3
    @12
    @0
    caddc
    oveq2
    fveq2d
    breq2d
    rspccv
    adantl
    3ad2ant3
    @11
    @18
    cc0
    @2
    cle
    @11
    @18
    cc0
    cabs
    cfv
    cc0
    @11
    @17
    cc0
    cabs
    @11
    @0
    @14
    negidd
    fveq2d
    abs0
    syl6eq
    breq2d
    sylibd
    mtod
    @0
    eldmgm
    sylanbrc
    rabssdv
    syl5eqss
end
