include "crh.mm"
include "co.mm"
include "wcel.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "wrex.mm"
include "cv.mm"
include "cinvr.mm"
include "cfv.mm"
include "cmulr.mm"
include "cur.mm"
include "elin.mm"
include "biimpi.mm"
include "adantl.mm"
include "simpld.mm"
include "crg.mm"
include "rhmrcl1.mm"
include "eqid.mm"
include "unitlinv.mm"
include "fveq2d.mm"
include "sylan.mm"
include "syldan.mm"
include "cbs.mm"
include "simpl.mm"
include "adantr.mm"
include "ringinvcl.mm"
include "syl2anc.mm"
include "unitcl.mm"
include "syl.mm"
include "rhmmul.mm"
include "syl3anc.mm"
include "simprd.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "rhmf.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "simplbda.mm"
include "fvex.mm"
include "elsn.mm"
include "sylib.mm"
include "oveq2d.mm"
include "rhmrcl2.mm"
include "ffvelrnd.mm"
include "ringrz.mm"
include "3eqtrd.mm"
include "rhm1.mm"
include "3eqtr3rd.mm"
include "reximdva0.mm"
include "id.mm"
include "rexlimivw.mm"

theorem kerunit
  let cR: class R
  let cS: class S
  let cU: class U
  let c.1: class .1.
  let cF: class F
  let c.0: class .0.
  let vx: setvar x
  assume kerunit.1: |- U = ( Unit ` R )
  assume kerunit.2: |- .0. = ( 0g ` S )
  assume kerunit.3: |- .1. = ( 1r ` S )


  assert |- ( ( F e. ( R RingHom S ) /\ ( U i^i ( `' F " { .0. } ) ) =/= (/) ) -> .1. = .0. )

  proof
    cF
    cR
    cS
    crh
    co
    wcel
    #
    cU
    cF
    ccnv
    c.0
    csn
    #
    cima
    #
    cin
    #
    c0
    wne
    wa
    c.1
    c.0
    wceq
    #
    vx
    @3
    wrex
    @4
    @0
    @4
    vx
    @3
    @0
    vx
    cv
    #
    @3
    wcel
    #
    wa
    #
    @5
    cR
    cinvr
    cfv
    #
    cfv
    #
    @5
    cR
    cmulr
    cfv
    #
    co
    #
    cF
    cfv
    #
    cR
    cur
    cfv
    #
    cF
    cfv
    #
    c.0
    c.1
    @0
    @6
    @5
    cU
    wcel
    #
    @12
    @14
    wceq
    #
    @7
    @15
    @5
    @2
    wcel
    #
    @6
    @15
    @17
    wa
    #
    @0
    @6
    @18
    @5
    cU
    @2
    elin
    biimpi
    adantl
    #
    simpld
    #
    @0
    cR
    crg
    wcel
    #
    @15
    @16
    cR
    cS
    cF
    rhmrcl1
    #
    @21
    @15
    wa
    @11
    @13
    cF
    cR
    @10
    cU
    @13
    @8
    @5
    kerunit.1
    @8
    eqid
    #
    @10
    eqid
    #
    @13
    eqid
    #
    unitlinv
    fveq2d
    sylan
    syldan
    @7
    @12
    @9
    cF
    cfv
    #
    @5
    cF
    cfv
    #
    cS
    cmulr
    cfv
    #
    co
    #
    @26
    c.0
    @28
    co
    #
    c.0
    @7
    @0
    @9
    cR
    cbs
    cfv
    #
    wcel
    #
    @5
    @31
    wcel
    #
    @12
    @29
    wceq
    @0
    @6
    simpl
    @7
    @21
    @15
    @32
    @0
    @21
    @6
    @22
    adantr
    @20
    @31
    cR
    cU
    @8
    @5
    kerunit.1
    @23
    @31
    eqid
    #
    ringinvcl
    syl2anc
    #
    @7
    @15
    @33
    @20
    @31
    cR
    cU
    @5
    @34
    kerunit.1
    unitcl
    syl
    @9
    @5
    cR
    cS
    @10
    @28
    cF
    @31
    @34
    @24
    @28
    eqid
    #
    rhmmul
    syl3anc
    @7
    @27
    c.0
    @26
    @28
    @7
    @27
    @1
    wcel
    #
    @27
    c.0
    wceq
    @0
    @6
    @17
    @37
    @7
    @15
    @17
    @19
    simprd
    @0
    @17
    @33
    @37
    @0
    @31
    cS
    cbs
    cfv
    #
    cF
    wf
    #
    cF
    @31
    wfn
    @17
    @33
    @37
    wa
    wb
    @31
    @38
    cR
    cS
    cF
    @34
    @38
    eqid
    #
    rhmf
    #
    @31
    @38
    cF
    ffn
    @31
    @5
    @1
    cF
    elpreima
    3syl
    simplbda
    syldan
    @27
    c.0
    @5
    cF
    fvex
    elsn
    sylib
    oveq2d
    @7
    cS
    crg
    wcel
    #
    @26
    @38
    wcel
    @30
    c.0
    wceq
    @0
    @42
    @6
    cR
    cS
    cF
    rhmrcl2
    adantr
    @7
    @31
    @38
    @9
    cF
    @0
    @39
    @6
    @41
    adantr
    @35
    ffvelrnd
    @38
    cS
    @28
    @26
    c.0
    @40
    @36
    kerunit.2
    ringrz
    syl2anc
    3eqtrd
    @0
    @14
    c.1
    wceq
    @6
    cR
    cS
    @13
    cF
    c.1
    @25
    kerunit.3
    rhm1
    adantr
    3eqtr3rd
    reximdva0
    @4
    @4
    vx
    @3
    @4
    id
    rexlimivw
    syl
end
