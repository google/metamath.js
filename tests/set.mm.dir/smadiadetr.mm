include "ccrg.mm"
include "wcel.mm"
include "cmat.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "wa.mm"
include "cmarrep.mm"
include "cmdat.mm"
include "csubma.mm"
include "csn.mm"
include "cdif.mm"
include "cmulr.mm"
include "wceq.mm"
include "wi.mm"
include "ccnfld.mm"
include "cif.mm"
include "w3a.mm"
include "3anass.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "fveq2.mm"
include "3anbi13d.mm"
include "syl5bbr.mm"
include "oveqd.mm"
include "fveq12d.mm"
include "eqidd.mm"
include "fveq1d.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "cncrng.mm"
include "elimel.mm"
include "smadiadetg0.mm"
include "dedth.mm"
include "impl.mm"

theorem smadiadetr
  let cR: class R
  let cS: class S
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( ( R e. CRing /\ M e. ( Base ` ( N Mat R ) ) ) /\ ( K e. N /\ S e. ( Base ` R ) ) ) -> ( ( N maDet R ) ` ( K ( M ( N matRRep R ) S ) K ) ) = ( S ( .r ` R ) ( ( ( N \ { K } ) maDet R ) ` ( K ( ( N subMat R ) ` M ) K ) ) ) )

  proof
    cR
    ccrg
    wcel
    #
    cM
    cN
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    #
    cK
    cN
    wcel
    #
    cS
    cR
    cbs
    cfv
    #
    wcel
    #
    wa
    #
    cK
    cK
    cM
    cS
    cN
    cR
    cmarrep
    co
    #
    co
    #
    co
    #
    cN
    cR
    cmdat
    co
    #
    cfv
    #
    cS
    cK
    cK
    cM
    cN
    cR
    csubma
    co
    #
    cfv
    #
    co
    #
    cN
    cK
    csn
    cdif
    #
    cR
    cmdat
    co
    #
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    wceq
    #
    @0
    @3
    @7
    wa
    #
    @21
    wi
    cM
    cN
    @0
    cR
    ccnfld
    cif
    #
    cmat
    co
    #
    cbs
    cfv
    #
    wcel
    #
    @4
    cS
    @23
    cbs
    cfv
    #
    wcel
    #
    w3a
    #
    cK
    cK
    cM
    cS
    cN
    @23
    cmarrep
    co
    #
    co
    #
    co
    #
    cN
    @23
    cmdat
    co
    #
    cfv
    #
    cS
    cK
    cK
    cM
    cN
    @23
    csubma
    co
    #
    cfv
    #
    co
    #
    @16
    @23
    cmdat
    co
    #
    cfv
    #
    @23
    cmulr
    cfv
    #
    co
    #
    wceq
    #
    wi
    cR
    ccnfld
    cR
    @23
    wceq
    #
    @22
    @29
    @21
    @42
    @22
    @3
    @4
    @6
    w3a
    @43
    @29
    @3
    @4
    @6
    3anass
    @43
    @3
    @26
    @6
    @28
    @4
    @43
    @2
    @25
    cM
    @43
    @1
    @24
    cbs
    cR
    @23
    cN
    cmat
    oveq2
    fveq2d
    eleq2d
    @43
    @5
    @27
    cS
    cR
    @23
    cbs
    fveq2
    eleq2d
    3anbi13d
    syl5bbr
    @43
    @12
    @34
    @20
    @41
    @43
    @10
    @32
    @11
    @33
    cR
    @23
    cN
    cmdat
    oveq2
    @43
    @9
    @31
    cK
    cK
    @43
    @8
    @30
    cM
    cS
    cR
    @23
    cN
    cmarrep
    oveq2
    oveqd
    oveqd
    fveq12d
    @43
    cS
    cS
    @18
    @39
    @19
    @40
    cR
    @23
    cmulr
    fveq2
    @43
    cS
    eqidd
    @43
    @15
    @37
    @17
    @38
    cR
    @23
    @16
    cmdat
    oveq2
    @43
    @14
    @36
    cK
    cK
    @43
    cM
    @13
    @35
    cR
    @23
    cN
    csubma
    oveq2
    fveq1d
    oveqd
    fveq12d
    oveq123d
    eqeq12d
    imbi12d
    @23
    cS
    cK
    cM
    cN
    cR
    ccnfld
    ccrg
    cncrng
    elimel
    smadiadetg0
    dedth
    impl
end
