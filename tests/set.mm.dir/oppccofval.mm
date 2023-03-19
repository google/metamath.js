include "cop.mm"
include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "c1st.mm"
include "co.mm"
include "ctpos.mm"
include "cco.mm"
include "cvv.mm"
include "cnx.mm"
include "chom.mm"
include "csts.mm"
include "cmpt2.mm"
include "wcel.mm"
include "wceq.mm"
include "cbs.mm"
include "elfvex.mm"
include "eleq2s.mm"
include "eqid.mm"
include "oppcval.mm"
include "3syl.mm"
include "fveq2d.mm"
include "ovex.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "mpt2ex.mm"
include "ccoid.mm"
include "setsid.mm"
include "mp2an.mm"
include "syl6eqr.mm"
include "wa.mm"
include "simprr.mm"
include "simprl.mm"
include "adantr.mm"
include "op2ndg.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "opeq12d.mm"
include "op1stg.mm"
include "oveq12d.mm"
include "tposeqd.mm"
include "opelxpi.mm"
include "tposex.mm"
include "a1i.mm"
include "ovmpt2d.mm"

theorem oppccofval
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vu: setvar u
  let vz: setvar z
  assume oppcco.b: |- B = ( Base ` C )
  assume oppcco.c: |- .x. = ( comp ` C )
  assume oppcco.o: |- O = ( oppCat ` C )
  assume oppcco.x: |- ( ph -> X e. B )
  assume oppcco.y: |- ( ph -> Y e. B )
  assume oppcco.z: |- ( ph -> Z e. B )


  assert |- ( ph -> ( <. X , Y >. ( comp ` O ) Z ) = tpos ( <. Z , Y >. .x. X ) )

  proof
    wph
    vu
    vz
    cX
    cY
    cop
    #
    cZ
    cB
    cB
    cxp
    #
    cB
    vz
    cv
    #
    vu
    cv
    #
    c2nd
    cfv
    #
    cop
    #
    @3
    c1st
    cfv
    #
    c.x
    co
    #
    ctpos
    #
    cZ
    cY
    cop
    #
    cX
    c.x
    co
    #
    ctpos
    #
    cO
    cco
    cfv
    #
    cvv
    wph
    @12
    cC
    cnx
    chom
    cfv
    cC
    chom
    cfv
    #
    ctpos
    cop
    #
    csts
    co
    #
    cnx
    cco
    cfv
    vu
    vz
    @1
    cB
    @8
    cmpt2
    #
    cop
    csts
    co
    #
    cco
    cfv
    #
    @16
    wph
    cO
    @17
    cco
    wph
    cX
    cB
    wcel
    #
    cC
    cvv
    wcel
    #
    cO
    @17
    wceq
    oppcco.x
    @20
    cX
    cC
    cbs
    cfv
    #
    cB
    cX
    cC
    cbs
    elfvex
    oppcco.b
    eleq2s
    vz
    vu
    cB
    cC
    c.x
    @13
    cO
    cvv
    oppcco.b
    @13
    eqid
    oppcco.c
    oppcco.o
    oppcval
    3syl
    fveq2d
    @15
    cvv
    wcel
    @16
    cvv
    wcel
    @16
    @18
    wceq
    cC
    @14
    csts
    ovex
    vu
    vz
    @1
    cB
    @8
    cB
    cB
    cB
    @21
    cvv
    oppcco.b
    cC
    cbs
    fvex
    eqeltri
    #
    @22
    xpex
    @22
    mpt2ex
    cvv
    @16
    cco
    cvv
    @15
    ccoid
    setsid
    mp2an
    syl6eqr
    wph
    @3
    @0
    wceq
    #
    @2
    cZ
    wceq
    #
    wa
    #
    wa
    #
    @7
    @10
    @26
    @5
    @9
    @6
    cX
    c.x
    @26
    @2
    cZ
    @4
    cY
    wph
    @23
    @24
    simprr
    @26
    @4
    @0
    c2nd
    cfv
    #
    cY
    @26
    @3
    @0
    c2nd
    wph
    @23
    @24
    simprl
    #
    fveq2d
    @26
    @19
    cY
    cB
    wcel
    #
    @27
    cY
    wceq
    wph
    @19
    @25
    oppcco.x
    adantr
    #
    wph
    @29
    @25
    oppcco.y
    adantr
    #
    cX
    cY
    cB
    cB
    op2ndg
    syl2anc
    eqtrd
    opeq12d
    @26
    @6
    @0
    c1st
    cfv
    #
    cX
    @26
    @3
    @0
    c1st
    @28
    fveq2d
    @26
    @19
    @29
    @32
    cX
    wceq
    @30
    @31
    cX
    cY
    cB
    cB
    op1stg
    syl2anc
    eqtrd
    oveq12d
    tposeqd
    wph
    @19
    @29
    @0
    @1
    wcel
    oppcco.x
    oppcco.y
    cX
    cY
    cB
    cB
    opelxpi
    syl2anc
    oppcco.z
    @11
    cvv
    wcel
    wph
    @10
    @9
    cX
    c.x
    ovex
    tposex
    a1i
    ovmpt2d
end
