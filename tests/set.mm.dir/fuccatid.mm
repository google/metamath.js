include "cv.mm"
include "cfunc.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cnat.mm"
include "w3a.mm"
include "cco.mm"
include "cfv.mm"
include "c1st.mm"
include "ccom.mm"
include "cvv.mm"
include "cbs.mm"
include "wceq.mm"
include "fucbas.mm"
include "a1i.mm"
include "chom.mm"
include "eqid.mm"
include "fuchom.mm"
include "eqidd.mm"
include "cfuc.mm"
include "ovex.mm"
include "eqeltri.mm"
include "biid.mm"
include "simpr.mm"
include "fucidcl.mm"
include "simpr31.mm"
include "fuclid.mm"
include "simpr32.mm"
include "fucrid.mm"
include "fuccocl.mm"
include "simpr33.mm"
include "fucass.mm"
include "iscatd2.mm"

theorem fuccatid
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cQ: class Q
  let c.1: class .1.
  let vf: setvar f
  let ve: setvar e
  let vg: setvar g
  let vh: setvar h
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  assume fuccat.q: |- Q = ( C FuncCat D )
  assume fuccat.r: |- ( ph -> C e. Cat )
  assume fuccat.s: |- ( ph -> D e. Cat )
  assume fuccatid.1: |- .1. = ( Id ` D )

  disjoint C f
  disjoint f ph
  disjoint D f
  disjoint Q f
  disjoint e g
  disjoint e h
  disjoint e r
  disjoint e s
  disjoint e t
  disjoint .1. e
  disjoint g h
  disjoint g r
  disjoint g s
  disjoint g t
  disjoint .1. g
  disjoint h r
  disjoint h s
  disjoint h t
  disjoint .1. h
  disjoint r s
  disjoint r t
  disjoint .1. r
  disjoint s t
  disjoint .1. s
  disjoint .1. t
  disjoint e f
  disjoint C e
  disjoint f g
  disjoint f h
  disjoint f r
  disjoint f s
  disjoint f t
  disjoint C g
  disjoint C h
  disjoint C r
  disjoint C s
  disjoint C t
  disjoint e ph
  disjoint g ph
  disjoint h ph
  disjoint ph r
  disjoint ph s
  disjoint ph t
  disjoint D e
  disjoint D g
  disjoint D h
  disjoint D r
  disjoint D s
  disjoint D t
  disjoint Q e
  disjoint Q g
  disjoint Q h
  disjoint Q r
  disjoint Q s
  disjoint Q t
  assert |- ( ph -> ( Q e. Cat /\ ( Id ` Q ) = ( f e. ( C Func D ) |-> ( .1. o. ( 1st ` f ) ) ) ) )

  proof
    wph
    ve
    cv
    #
    cC
    cD
    cfunc
    co
    #
    wcel
    vf
    cv
    #
    @1
    wcel
    #
    wa
    #
    vg
    cv
    #
    @1
    wcel
    vh
    cv
    #
    @1
    wcel
    wa
    #
    vr
    cv
    #
    @0
    @2
    cC
    cD
    cnat
    co
    #
    co
    wcel
    #
    vs
    cv
    #
    @2
    @5
    @9
    co
    wcel
    #
    vt
    cv
    #
    @5
    @6
    @9
    co
    wcel
    #
    w3a
    w3a
    #
    ve
    vf
    vg
    vh
    @1
    cQ
    cQ
    cco
    cfv
    #
    c.1
    @2
    c1st
    cfv
    ccom
    vr
    vs
    vt
    @9
    cvv
    @1
    cQ
    cbs
    cfv
    wceq
    wph
    cC
    cD
    cQ
    fuccat.q
    fucbas
    a1i
    @9
    cQ
    chom
    cfv
    wceq
    wph
    cC
    cD
    cQ
    @9
    fuccat.q
    @9
    eqid
    #
    fuchom
    a1i
    wph
    @16
    eqidd
    cQ
    cvv
    wcel
    wph
    cQ
    cC
    cD
    cfuc
    co
    cvv
    fuccat.q
    cC
    cD
    cfuc
    ovex
    eqeltri
    a1i
    @15
    biid
    wph
    @3
    wa
    cC
    cD
    cQ
    c.1
    @2
    @9
    fuccat.q
    @17
    fuccatid.1
    wph
    @3
    simpr
    fucidcl
    wph
    @15
    wa
    #
    cC
    cD
    cQ
    @8
    @16
    c.1
    @0
    @2
    @9
    fuccat.q
    @17
    @16
    eqid
    #
    fuccatid.1
    @10
    @12
    @14
    @4
    @7
    wph
    simpr31
    #
    fuclid
    @18
    cC
    cD
    cQ
    @11
    @16
    c.1
    @2
    @5
    @9
    fuccat.q
    @17
    @19
    fuccatid.1
    @10
    @12
    @14
    @4
    @7
    wph
    simpr32
    #
    fucrid
    @18
    cC
    cD
    cQ
    @8
    @11
    @16
    @0
    @2
    @5
    @9
    fuccat.q
    @17
    @19
    @20
    @21
    fuccocl
    @18
    cC
    cD
    cQ
    @8
    @11
    @16
    @13
    @0
    @2
    @5
    @6
    @9
    fuccat.q
    @17
    @19
    @20
    @21
    @10
    @12
    @14
    @4
    @7
    wph
    simpr33
    fucass
    iscatd2
end
