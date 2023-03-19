include "cdr.mm"
include "wcel.mm"
include "cchr.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cq.mm"
include "cv.mm"
include "cnumer.mm"
include "cdenom.mm"
include "co.mm"
include "cqqh.mm"
include "qqhval2.mm"
include "crg.mm"
include "cui.mm"
include "drngring.mm"
include "adantr.mm"
include "cz.mm"
include "zring.mm"
include "crh.mm"
include "wf.mm"
include "zrhrhm.mm"
include "zringbas.mm"
include "rhmf.mm"
include "3syl.mm"
include "qnumcl.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "c0g.mm"
include "wne.mm"
include "simpll.mm"
include "cn.mm"
include "qdencl.mm"
include "nnzd.mm"
include "csn.mm"
include "ccnv.mm"
include "cima.mm"
include "wn.mm"
include "nnne0d.mm"
include "neneqd.mm"
include "fvex.mm"
include "elsn.mm"
include "sylnibr.mm"
include "eqid.mm"
include "zrhker.mm"
include "biimpa.mm"
include "sylan.mm"
include "neleqtrrd.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "elpreima.mm"
include "biimpar.mm"
include "expr.mm"
include "con3dimp.mm"
include "syl21anc.mm"
include "sylnib.mm"
include "neqned.mm"
include "drngunit.mm"
include "syl12anc.mm"
include "dvrcl.mm"
include "syl3anc.mm"
include "fmpt3d.mm"

theorem qqhf
  let cB: class B
  let c.dv: class ./
  let cR: class R
  let cL: class L
  let ve: setvar e
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let cQ: class Q
  assume qqhval2.0: |- B = ( Base ` R )
  assume qqhval2.1: |- ./ = ( /r ` R )
  assume qqhval2.2: |- L = ( ZRHom ` R )


  assert |- ( ( R e. DivRing /\ ( chr ` R ) = 0 ) -> ( QQHom ` R ) : QQ --> B )

  proof
    cR
    cdr
    wcel
    #
    cR
    cchr
    cfv
    cc0
    wceq
    #
    wa
    #
    vq
    cq
    vq
    cv
    #
    cnumer
    cfv
    #
    cL
    cfv
    #
    @3
    cdenom
    cfv
    #
    cL
    cfv
    #
    c.dv
    co
    #
    cB
    cR
    cqqh
    cfv
    cB
    c.dv
    cR
    cL
    vq
    qqhval2.0
    qqhval2.1
    qqhval2.2
    qqhval2
    @2
    @3
    cq
    wcel
    #
    wa
    #
    cR
    crg
    wcel
    #
    @5
    cB
    wcel
    @7
    cR
    cui
    cfv
    #
    wcel
    #
    @8
    cB
    wcel
    @2
    @11
    @9
    @0
    @11
    @1
    cR
    drngring
    #
    adantr
    adantr
    #
    @10
    cz
    cB
    @4
    cL
    @10
    @11
    cL
    zring
    cR
    crh
    co
    wcel
    #
    cz
    cB
    cL
    wf
    #
    @15
    cR
    cL
    qqhval2.2
    zrhrhm
    #
    cz
    cB
    zring
    cR
    cL
    zringbas
    qqhval2.0
    rhmf
    #
    3syl
    #
    @9
    @4
    cz
    wcel
    @2
    @3
    qnumcl
    adantl
    ffvelrnd
    @10
    @0
    @7
    cB
    wcel
    #
    @7
    cR
    c0g
    cfv
    #
    wne
    #
    @13
    @0
    @1
    @9
    simpll
    #
    @10
    cz
    cB
    @6
    cL
    @20
    @10
    @6
    @9
    @6
    cn
    wcel
    @2
    @3
    qdencl
    adantl
    #
    nnzd
    #
    ffvelrnd
    @10
    @7
    @22
    @10
    @7
    @22
    csn
    #
    wcel
    #
    @7
    @22
    wceq
    @10
    @0
    @6
    cz
    wcel
    #
    @6
    cL
    ccnv
    @27
    cima
    #
    wcel
    #
    wn
    @28
    wn
    @24
    @26
    @10
    @30
    cc0
    csn
    #
    @6
    @10
    @6
    cc0
    wceq
    @6
    @32
    wcel
    @10
    @6
    cc0
    @10
    @6
    @25
    nnne0d
    neneqd
    @6
    cc0
    @3
    cdenom
    fvex
    elsn
    sylnibr
    @2
    @30
    @32
    wceq
    #
    @9
    @0
    @11
    @1
    @33
    @14
    @11
    @1
    @33
    cB
    cR
    cL
    @22
    qqhval2.0
    qqhval2.2
    @22
    eqid
    #
    zrhker
    biimpa
    sylan
    adantr
    neleqtrrd
    @0
    @29
    wa
    @28
    @31
    @0
    @29
    @28
    @31
    @0
    @31
    @29
    @28
    wa
    #
    @0
    @11
    cL
    cz
    wfn
    #
    @31
    @35
    wb
    @14
    @11
    @16
    @17
    @36
    @18
    @19
    cz
    cB
    cL
    ffn
    3syl
    cz
    @6
    @27
    cL
    elpreima
    3syl
    biimpar
    expr
    con3dimp
    syl21anc
    @7
    @22
    @6
    cL
    fvex
    elsn
    sylnib
    neqned
    @0
    @13
    @21
    @23
    wa
    cB
    cR
    @12
    @7
    @22
    qqhval2.0
    @12
    eqid
    #
    @34
    drngunit
    biimpar
    syl12anc
    cB
    c.dv
    cR
    @12
    @5
    @7
    qqhval2.0
    @37
    qqhval2.1
    dvrcl
    syl3anc
    fmpt3d
end
