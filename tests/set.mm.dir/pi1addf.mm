include "cxp.mm"
include "wf.mm"
include "cuni.mm"
include "cphtpc.mm"
include "cfv.mm"
include "cin.mm"
include "cqs.mm"
include "comi.mm"
include "co.mm"
include "cplusg.mm"
include "cvv.mm"
include "cqus.mm"
include "cbs.mm"
include "eqidd.mm"
include "fvexd.mm"
include "ovexd.mm"
include "cima.mm"
include "wss.mm"
include "cii.mm"
include "ccn.mm"
include "eqid.mm"
include "wceq.mm"
include "a1i.mm"
include "pi1blem.mm"
include "simpld.mm"
include "qusin.mm"
include "pi1val.mm"
include "pi1buni.mm"
include "sqxpeqd.mm"
include "ineq2d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "wer.mm"
include "phtpcer.mm"
include "simprd.mm"
include "eqsstrd.mm"
include "erinxp.mm"
include "cv.mm"
include "pi1cpbl.mm"
include "wcel.mm"
include "wa.mm"
include "cpco.mm"
include "ctopon.mm"
include "adantr.mm"
include "om1plusg.mm"
include "oveqd.mm"
include "simprl.mm"
include "simprr.mm"
include "om1addcl.mm"
include "eqeltrrd.mm"
include "qusaddf.mm"
include "pi1bas3.mm"
include "feq2d.mm"
include "mpbird.mm"
include "feq3d.mm"

theorem pi1addf
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cJ: class J
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cF: class F
  let vf: setvar f
  let cM: class M
  let cN: class N
  assume elpi1.g: |- G = ( J pi1 Y )
  assume elpi1.b: |- B = ( Base ` G )
  assume elpi1.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume elpi1.2: |- ( ph -> Y e. X )
  assume pi1addf.p: |- .+ = ( +g ` G )


  assert |- ( ph -> .+ : ( B X. B ) --> B )

  proof
    wph
    cB
    cB
    cxp
    #
    cB
    c.pl
    wf
    @0
    cB
    cuni
    #
    cJ
    cphtpc
    cfv
    #
    @1
    @1
    cxp
    #
    cin
    #
    cqs
    #
    c.pl
    wf
    #
    wph
    @6
    @5
    @5
    cxp
    #
    @5
    c.pl
    wf
    wph
    @4
    cJ
    cY
    comi
    co
    #
    c.pl
    @8
    cplusg
    cfv
    #
    cG
    @1
    cvv
    vd
    vc
    va
    vb
    wph
    @8
    @2
    cqus
    co
    #
    @8
    @2
    @8
    cbs
    cfv
    #
    @11
    cxp
    #
    cin
    #
    cqus
    co
    cG
    @8
    @4
    cqus
    co
    wph
    @2
    @8
    @10
    @11
    cvv
    cvv
    wph
    @10
    eqidd
    wph
    @11
    eqidd
    #
    wph
    cJ
    cphtpc
    fvexd
    wph
    cJ
    cY
    comi
    ovexd
    #
    wph
    @2
    @11
    cima
    @11
    wss
    #
    @11
    cii
    cJ
    ccn
    co
    #
    wss
    #
    wph
    cB
    cG
    cJ
    @11
    @8
    cX
    cY
    elpi1.g
    elpi1.1
    elpi1.2
    @8
    eqid
    #
    cB
    cG
    cbs
    cfv
    wceq
    wph
    elpi1.b
    a1i
    #
    @14
    pi1blem
    #
    simpld
    qusin
    wph
    cG
    cJ
    @8
    cX
    cY
    elpi1.g
    elpi1.1
    elpi1.2
    @19
    pi1val
    wph
    @4
    @13
    @8
    cqus
    wph
    @3
    @12
    @2
    wph
    @1
    @11
    wph
    cB
    cG
    cJ
    @11
    @8
    cX
    cY
    elpi1.g
    elpi1.1
    elpi1.2
    @19
    @20
    @14
    pi1buni
    #
    sqxpeqd
    ineq2d
    oveq2d
    3eqtr4d
    @22
    wph
    @17
    @1
    @2
    @17
    @2
    wer
    wph
    cJ
    phtpcer
    a1i
    wph
    @1
    @11
    @17
    @22
    wph
    @16
    @18
    @21
    simprd
    eqsstrd
    erinxp
    @15
    wph
    cB
    vb
    cv
    @9
    vd
    cv
    #
    @4
    cG
    cJ
    va
    cv
    vc
    cv
    #
    @8
    cX
    cY
    elpi1.g
    elpi1.1
    elpi1.2
    @20
    @4
    eqid
    #
    @19
    @9
    eqid
    #
    pi1cpbl
    wph
    @24
    @1
    wcel
    #
    @23
    @1
    wcel
    #
    wa
    #
    wa
    #
    @24
    @23
    cJ
    cpco
    cfv
    #
    co
    @24
    @23
    @9
    co
    @1
    @30
    @31
    @9
    @24
    @23
    @30
    cJ
    @8
    cX
    cY
    @19
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    @29
    elpi1.1
    adantr
    #
    wph
    cY
    cX
    wcel
    @29
    elpi1.2
    adantr
    #
    om1plusg
    oveqd
    @30
    @1
    @24
    cJ
    @23
    @8
    cX
    cY
    @19
    @32
    @33
    wph
    @1
    @11
    wceq
    @29
    @22
    adantr
    wph
    @27
    @28
    simprl
    wph
    @27
    @28
    simprr
    om1addcl
    eqeltrrd
    @26
    pi1addf.p
    qusaddf
    wph
    @0
    @7
    @5
    c.pl
    wph
    cB
    @5
    wph
    cB
    @4
    cG
    cJ
    cX
    cY
    elpi1.g
    elpi1.1
    elpi1.2
    @20
    @25
    pi1bas3
    #
    sqxpeqd
    feq2d
    mpbird
    wph
    cB
    @5
    c.pl
    @0
    @34
    feq3d
    mpbird
end
