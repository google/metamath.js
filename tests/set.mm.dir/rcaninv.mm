include "co.mm"
include "wceq.mm"
include "wa.mm"
include "cfv.mm"
include "cop.mm"
include "cco.mm"
include "ccid.mm"
include "chom.mm"
include "eqid.mm"
include "ciso.mm"
include "isohom.mm"
include "sseldd.mm"
include "invf.mm"
include "ffvelrnd.mm"
include "catass.mm"
include "invcoisoid.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "catrid.mm"
include "3eqtr2rd.mm"
include "adantr.mm"
include "eqcomi.mm"
include "a1i.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "simpr.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "oveqi.mm"
include "oveq1i.mm"
include "syl5eqel.mm"
include "oveq2i.mm"
include "3eqtrd.mm"
include "ex.mm"

theorem rcaninv
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cR: class R
  let cF: class F
  let cG: class G
  let cH: class H
  let cN: class N
  let cX: class X
  let cY: class Y
  let c.op: class .o.
  let cZ: class Z
  assume rcaninv.b: |- B = ( Base ` C )
  assume rcaninv.n: |- N = ( Inv ` C )
  assume rcaninv.c: |- ( ph -> C e. Cat )
  assume rcaninv.x: |- ( ph -> X e. B )
  assume rcaninv.y: |- ( ph -> Y e. B )
  assume rcaninv.z: |- ( ph -> Z e. B )
  assume rcaninv.f: |- ( ph -> F e. ( Y ( Iso ` C ) X ) )
  assume rcaninv.g: |- ( ph -> G e. ( Y ( Hom ` C ) Z ) )
  assume rcaninv.h: |- ( ph -> H e. ( Y ( Hom ` C ) Z ) )
  assume rcaninv.1: |- R = ( ( Y N X ) ` F )
  assume rcaninv.o: |- .o. = ( <. X , Y >. ( comp ` C ) Z )


  assert |- ( ph -> ( ( G .o. R ) = ( H .o. R ) -> G = H ) )

  proof
    wph
    cG
    cR
    c.op
    co
    #
    cH
    cR
    c.op
    co
    #
    wceq
    #
    cG
    cH
    wceq
    wph
    @2
    wa
    #
    cG
    cG
    cF
    cY
    cX
    cN
    co
    #
    cfv
    #
    cX
    cY
    cop
    cZ
    cC
    cco
    cfv
    #
    co
    #
    co
    #
    cF
    cY
    cX
    cop
    #
    cZ
    @6
    co
    #
    co
    #
    @1
    cF
    @10
    co
    #
    cH
    wph
    cG
    @11
    wceq
    @2
    wph
    @11
    cG
    @5
    cF
    @9
    cY
    @6
    co
    #
    co
    #
    cY
    cY
    cop
    cZ
    @6
    co
    #
    co
    cG
    cY
    cC
    ccid
    cfv
    #
    cfv
    #
    @15
    co
    cG
    wph
    cB
    cC
    @6
    cF
    @5
    cC
    chom
    cfv
    #
    cG
    cZ
    cY
    cX
    cY
    rcaninv.b
    @18
    eqid
    #
    @6
    eqid
    #
    rcaninv.c
    rcaninv.y
    rcaninv.x
    rcaninv.y
    wph
    cY
    cX
    cC
    ciso
    cfv
    #
    co
    #
    cY
    cX
    @18
    co
    cF
    wph
    cB
    cC
    @18
    @21
    cY
    cX
    rcaninv.b
    @19
    @21
    eqid
    #
    rcaninv.c
    rcaninv.y
    rcaninv.x
    isohom
    rcaninv.f
    sseldd
    #
    wph
    cX
    cY
    @21
    co
    #
    cX
    cY
    @18
    co
    #
    @5
    wph
    cB
    cC
    @18
    @21
    cX
    cY
    rcaninv.b
    @19
    @23
    rcaninv.c
    rcaninv.x
    rcaninv.y
    isohom
    wph
    @22
    @25
    cF
    @4
    wph
    cB
    cC
    @21
    cN
    cY
    cX
    rcaninv.b
    rcaninv.n
    rcaninv.c
    rcaninv.y
    rcaninv.x
    @23
    invf
    rcaninv.f
    ffvelrnd
    sseldd
    #
    rcaninv.z
    rcaninv.g
    catass
    wph
    @17
    @14
    cG
    @15
    wph
    @14
    @17
    wph
    cB
    cC
    @16
    cF
    @21
    cN
    cY
    cX
    @13
    rcaninv.b
    @23
    rcaninv.n
    rcaninv.c
    rcaninv.y
    rcaninv.x
    rcaninv.f
    @16
    eqid
    #
    @13
    eqid
    invcoisoid
    #
    eqcomd
    oveq2d
    wph
    cB
    cC
    @6
    @16
    cG
    @18
    cY
    cZ
    rcaninv.b
    @19
    @28
    rcaninv.c
    rcaninv.y
    @20
    rcaninv.z
    rcaninv.g
    catrid
    3eqtr2rd
    adantr
    @3
    @8
    @1
    cF
    @10
    @3
    @8
    @0
    @1
    wph
    @8
    @0
    wceq
    @2
    wph
    cG
    cG
    @5
    cR
    @7
    c.op
    @7
    c.op
    wceq
    wph
    c.op
    @7
    rcaninv.o
    eqcomi
    a1i
    wph
    cG
    eqidd
    @5
    cR
    wceq
    wph
    cR
    @5
    rcaninv.1
    eqcomi
    a1i
    oveq123d
    adantr
    wph
    @2
    simpr
    eqtrd
    oveq1d
    wph
    @12
    cH
    wceq
    @2
    wph
    @12
    cH
    cR
    @7
    co
    #
    cF
    @10
    co
    #
    cH
    @17
    @15
    co
    #
    cH
    @12
    @31
    wceq
    wph
    @1
    @30
    cF
    @10
    c.op
    @7
    cH
    cR
    rcaninv.o
    oveqi
    oveq1i
    a1i
    wph
    @31
    cH
    cR
    cF
    @13
    co
    #
    @15
    co
    #
    cH
    @14
    @15
    co
    #
    @32
    wph
    cB
    cC
    @6
    cF
    cR
    @18
    cH
    cZ
    cY
    cX
    cY
    rcaninv.b
    @19
    @20
    rcaninv.c
    rcaninv.y
    rcaninv.x
    rcaninv.y
    @24
    wph
    cR
    @5
    @26
    rcaninv.1
    @27
    syl5eqel
    rcaninv.z
    rcaninv.h
    catass
    @34
    @35
    wceq
    wph
    @33
    @14
    cH
    @15
    cR
    @5
    cF
    @13
    rcaninv.1
    oveq1i
    oveq2i
    a1i
    wph
    @14
    @17
    cH
    @15
    @29
    oveq2d
    3eqtrd
    wph
    cB
    cC
    @6
    @16
    cH
    @18
    cY
    cZ
    rcaninv.b
    @19
    @28
    rcaninv.c
    rcaninv.y
    @20
    rcaninv.z
    rcaninv.h
    catrid
    3eqtrd
    adantr
    3eqtrd
    ex
end
