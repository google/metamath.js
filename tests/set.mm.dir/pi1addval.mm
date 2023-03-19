include "cphtpc.mm"
include "cfv.mm"
include "cuni.mm"
include "cxp.mm"
include "cin.mm"
include "cec.mm"
include "co.mm"
include "comi.mm"
include "cplusg.mm"
include "cpco.mm"
include "wcel.mm"
include "wceq.mm"
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
include "wa.mm"
include "om1plusg.mm"
include "adantr.mm"
include "oveqd.mm"
include "ctopon.mm"
include "simprl.mm"
include "simprr.mm"
include "om1addcl.mm"
include "eqeltrrd.mm"
include "qusaddval.mm"
include "mpd3an23.mm"
include "imaeq2d.mm"
include "3sstr4d.mm"
include "ecinxp.mm"
include "syl2anc.mm"
include "oveq12d.mm"
include "eceq1d.mm"
include "eqtrd.mm"

theorem pi1addval
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cJ: class J
  let cM: class M
  let cN: class N
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let cF: class F
  let vf: setvar f
  assume elpi1.g: |- G = ( J pi1 Y )
  assume elpi1.b: |- B = ( Base ` G )
  assume elpi1.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume elpi1.2: |- ( ph -> Y e. X )
  assume pi1addf.p: |- .+ = ( +g ` G )
  assume pi1addval.3: |- ( ph -> M e. U. B )
  assume pi1addval.4: |- ( ph -> N e. U. B )


  assert |- ( ph -> ( [ M ] ( ~=ph ` J ) .+ [ N ] ( ~=ph ` J ) ) = [ ( M ( *p ` J ) N ) ] ( ~=ph ` J ) )

  proof
    wph
    cM
    cJ
    cphtpc
    cfv
    #
    cB
    cuni
    #
    @1
    cxp
    #
    cin
    #
    cec
    #
    cN
    @3
    cec
    #
    c.pl
    co
    #
    cM
    cN
    cJ
    cY
    comi
    co
    #
    cplusg
    cfv
    #
    co
    #
    @3
    cec
    #
    cM
    @0
    cec
    #
    cN
    @0
    cec
    #
    c.pl
    co
    cM
    cN
    cJ
    cpco
    cfv
    #
    co
    #
    @0
    cec
    #
    wph
    cM
    @1
    wcel
    #
    cN
    @1
    wcel
    #
    @6
    @10
    wceq
    pi1addval.3
    pi1addval.4
    wph
    @3
    @7
    c.pl
    @8
    cG
    @1
    cM
    cN
    cvv
    vd
    vc
    va
    vb
    wph
    @7
    @0
    cqus
    co
    #
    @7
    @0
    @7
    cbs
    cfv
    #
    @19
    cxp
    #
    cin
    #
    cqus
    co
    cG
    @7
    @3
    cqus
    co
    wph
    @0
    @7
    @18
    @19
    cvv
    cvv
    wph
    @18
    eqidd
    wph
    @19
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
    @0
    @19
    cima
    #
    @19
    wss
    #
    @19
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
    @19
    @7
    cX
    cY
    elpi1.g
    elpi1.1
    elpi1.2
    @7
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
    @22
    pi1blem
    #
    simpld
    #
    qusin
    wph
    cG
    cJ
    @7
    cX
    cY
    elpi1.g
    elpi1.1
    elpi1.2
    @28
    pi1val
    wph
    @3
    @21
    @7
    cqus
    wph
    @2
    @20
    @0
    wph
    @1
    @19
    wph
    cB
    cG
    cJ
    @19
    @7
    cX
    cY
    elpi1.g
    elpi1.1
    elpi1.2
    @28
    @29
    @22
    pi1buni
    #
    sqxpeqd
    ineq2d
    oveq2d
    3eqtr4d
    @32
    wph
    @26
    @1
    @0
    @26
    @0
    wer
    wph
    cJ
    phtpcer
    a1i
    wph
    @1
    @19
    @26
    @32
    wph
    @25
    @27
    @30
    simprd
    eqsstrd
    erinxp
    @23
    wph
    cB
    vb
    cv
    @8
    vd
    cv
    #
    @3
    cG
    cJ
    va
    cv
    vc
    cv
    #
    @7
    cX
    cY
    elpi1.g
    elpi1.1
    elpi1.2
    @29
    @3
    eqid
    @28
    @8
    eqid
    #
    pi1cpbl
    wph
    @34
    @1
    wcel
    #
    @33
    @1
    wcel
    #
    wa
    #
    wa
    #
    @34
    @33
    @13
    co
    @34
    @33
    @8
    co
    @1
    @39
    @13
    @8
    @34
    @33
    wph
    @13
    @8
    wceq
    @38
    wph
    cJ
    @7
    cX
    cY
    @28
    elpi1.1
    elpi1.2
    om1plusg
    #
    adantr
    oveqd
    @39
    @1
    @34
    cJ
    @33
    @7
    cX
    cY
    @28
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    @38
    elpi1.1
    adantr
    wph
    cY
    cX
    wcel
    @38
    elpi1.2
    adantr
    wph
    @1
    @19
    wceq
    @38
    @32
    adantr
    wph
    @36
    @37
    simprl
    wph
    @36
    @37
    simprr
    om1addcl
    eqeltrrd
    @35
    pi1addf.p
    qusaddval
    mpd3an23
    wph
    @11
    @4
    @12
    @5
    c.pl
    wph
    @0
    @1
    cima
    #
    @1
    wss
    #
    @16
    @11
    @4
    wceq
    wph
    @24
    @19
    @41
    @1
    @31
    wph
    @1
    @19
    @0
    @32
    imaeq2d
    @32
    3sstr4d
    #
    pi1addval.3
    @1
    cM
    @0
    ecinxp
    syl2anc
    wph
    @42
    @17
    @12
    @5
    wceq
    @43
    pi1addval.4
    @1
    cN
    @0
    ecinxp
    syl2anc
    oveq12d
    wph
    @15
    @14
    @3
    cec
    #
    @10
    wph
    @42
    @14
    @1
    wcel
    @15
    @44
    wceq
    @43
    wph
    @1
    cM
    cJ
    cN
    @7
    cX
    cY
    @28
    elpi1.1
    elpi1.2
    @32
    pi1addval.3
    pi1addval.4
    om1addcl
    @1
    @14
    @0
    ecinxp
    syl2anc
    wph
    @14
    @9
    @3
    wph
    @13
    @8
    cM
    cN
    @40
    oveqd
    eceq1d
    eqtrd
    3eqtr4d
end
