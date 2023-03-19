include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "clss.mm"
include "cfv.mm"
include "clmod.mm"
include "lmhmlmod2.mm"
include "eqid.mm"
include "lsssn0.mm"
include "syl.mm"
include "lmhmpreima.mm"
include "mpdan.mm"
include "syl5eqel.mm"

theorem lmhmkerlss
  let cS: class S
  let cT: class T
  let cU: class U
  let cF: class F
  let cK: class K
  let c.0: class .0.
  assume lmhmkerlss.k: |- K = ( `' F " { .0. } )
  assume lmhmkerlss.z: |- .0. = ( 0g ` T )
  assume lmhmkerlss.u: |- U = ( LSubSp ` S )


  assert |- ( F e. ( S LMHom T ) -> K e. U )

  proof
    cF
    cS
    cT
    clmhm
    co
    wcel
    #
    cK
    cF
    ccnv
    c.0
    csn
    #
    cima
    #
    cU
    lmhmkerlss.k
    @0
    @1
    cT
    clss
    cfv
    #
    wcel
    #
    @2
    cU
    wcel
    @0
    cT
    clmod
    wcel
    @4
    cS
    cT
    cF
    lmhmlmod2
    @3
    cT
    c.0
    lmhmkerlss.z
    @3
    eqid
    #
    lsssn0
    syl
    cS
    cT
    @1
    cF
    cU
    @3
    lmhmkerlss.u
    @5
    lmhmpreima
    mpdan
    syl5eqel
end
