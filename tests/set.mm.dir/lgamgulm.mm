include "caddc.mm"
include "cof.mm"
include "c1.mm"
include "cseq.mm"
include "culm.mm"
include "cfv.mm"
include "cdm.mm"
include "wcel.mm"
include "cmpt.mm"
include "wbr.mm"
include "cabs.mm"
include "cv.mm"
include "cle.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wi.mm"
include "cn.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cexp.mm"
include "cdiv.mm"
include "clog.mm"
include "cpi.mm"
include "cif.mm"
include "eqid.mm"
include "lgamgulmlem6.mm"
include "simpld.mm"

theorem lgamgulm
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cR: class R
  let cU: class U
  let vk: setvar k
  let vm: setvar m
  let cG: class G
  let vn: setvar n
  let vr: setvar r
  let vy: setvar y
  let vt: setvar t
  let cN: class N
  let cA: class A
  let cO: class O
  let cT: class T
  assume lgamgulm.r: |- ( ph -> R e. NN )
  assume lgamgulm.u: |- U = { x e. CC | ( ( abs ` x ) <_ R /\ A. k e. NN0 ( 1 / R ) <_ ( abs ` ( x + k ) ) ) }
  assume lgamgulm.g: |- G = ( m e. NN |-> ( z e. U |-> ( ( z x. ( log ` ( ( m + 1 ) / m ) ) ) - ( log ` ( ( z / m ) + 1 ) ) ) ) )

  disjoint k m
  disjoint k x
  disjoint k z
  disjoint R k
  disjoint m x
  disjoint m z
  disjoint R m
  disjoint x z
  disjoint R x
  disjoint R z
  disjoint U m
  disjoint U z
  disjoint m ph
  disjoint ph x
  disjoint ph z
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
  disjoint k n
  disjoint k r
  disjoint k t
  disjoint k y
  disjoint m n
  disjoint m r
  disjoint m t
  disjoint m y
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
  disjoint y z
  disjoint R y
  disjoint U n
  disjoint U r
  disjoint U t
  disjoint U y
  disjoint A k
  disjoint A m
  disjoint A t
  disjoint A x
  disjoint A y
  disjoint O n
  disjoint O r
  disjoint O y
  disjoint n ph
  disjoint ph r
  disjoint ph t
  disjoint ph y
  disjoint T n
  disjoint T r
  disjoint T y
  assert |- ( ph -> seq 1 ( oF + , G ) e. dom ( ~~>u ` U ) )

  proof
    wph
    caddc
    cof
    cG
    c1
    cseq
    #
    cU
    culm
    cfv
    #
    cdm
    wcel
    @0
    vz
    cU
    c1
    cmpt
    @1
    wbr
    c1
    cabs
    cfv
    vr
    cv
    cle
    wbr
    vz
    cU
    wral
    vr
    cr
    wrex
    wi
    wph
    vx
    vz
    cR
    vm
    cn
    c2
    cR
    cmul
    co
    vm
    cv
    #
    cle
    wbr
    cR
    c2
    cR
    c1
    caddc
    co
    #
    cmul
    co
    @2
    c2
    cexp
    co
    cdiv
    co
    cmul
    co
    cR
    @2
    c1
    caddc
    co
    @2
    cdiv
    co
    clog
    cfv
    cmul
    co
    @3
    @2
    cmul
    co
    clog
    cfv
    cpi
    caddc
    co
    caddc
    co
    cif
    cmpt
    #
    cU
    vk
    vm
    cG
    c1
    vr
    lgamgulm.r
    lgamgulm.u
    lgamgulm.g
    @4
    eqid
    lgamgulmlem6
    simpld
end
