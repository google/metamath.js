include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cn0.mm"
include "c1o.mm"
include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "cmpt.mm"
include "ccom.mm"
include "cof.mm"
include "cco1.mm"
include "cfv.mm"
include "cmpl.mm"
include "eqid.mm"
include "cps1.mm"
include "ply1bas.mm"
include "ply1plusg.mm"
include "simp2.mm"
include "simp3.mm"
include "mpladd.mm"
include "coeq1d.mm"
include "cmap.mm"
include "cvv.mm"
include "wfn.mm"
include "cbs.mm"
include "wf.mm"
include "ply1basf.mm"
include "ffn.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "3ad2ant3.mm"
include "wf1o.mm"
include "c0.mm"
include "df1o2.mm"
include "nn0ex.mm"
include "0ex.mm"
include "mapsnf1o3.mm"
include "f1of.mm"
include "mp1i.mm"
include "ovexd.mm"
include "a1i.mm"
include "inidm.mm"
include "ofco.mm"
include "eqtrd.mm"
include "wceq.mm"
include "ply1ring.mm"
include "ringacl.mm"
include "syl3an1.mm"
include "coe1fval2.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem coe1add
  let cB: class B
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let cF: class F
  let cG: class G
  let cY: class Y
  let va: setvar a
  assume coe1add.y: |- Y = ( Poly1 ` R )
  assume coe1add.b: |- B = ( Base ` Y )
  assume coe1add.p: |- .+b = ( +g ` Y )
  assume coe1add.q: |- .+ = ( +g ` R )


  assert |- ( ( R e. Ring /\ F e. B /\ G e. B ) -> ( coe1 ` ( F .+b G ) ) = ( ( coe1 ` F ) oF .+ ( coe1 ` G ) ) )

  proof
    cR
    crg
    wcel
    #
    cF
    cB
    wcel
    #
    cG
    cB
    wcel
    #
    w3a
    #
    cF
    cG
    c.pb
    co
    #
    va
    cn0
    c1o
    va
    cv
    csn
    cxp
    cmpt
    #
    ccom
    #
    cF
    @5
    ccom
    #
    cG
    @5
    ccom
    #
    c.pl
    cof
    #
    co
    #
    @4
    cco1
    cfv
    #
    cF
    cco1
    cfv
    #
    cG
    cco1
    cfv
    #
    @9
    co
    @3
    @6
    cF
    cG
    @9
    co
    #
    @5
    ccom
    @10
    @3
    @4
    @14
    @5
    @3
    cB
    c1o
    cR
    cmpl
    co
    #
    c.pl
    c.pb
    cR
    c1o
    cF
    cG
    @15
    eqid
    #
    cY
    cR
    cR
    cps1
    cfv
    #
    cB
    coe1add.y
    @17
    eqid
    coe1add.b
    ply1bas
    coe1add.q
    c.pb
    cR
    @15
    cY
    coe1add.y
    @16
    coe1add.p
    ply1plusg
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    mpladd
    coeq1d
    @3
    cn0
    c1o
    cmap
    co
    #
    @18
    @18
    cn0
    c.pl
    cF
    cG
    @5
    cvv
    cvv
    cvv
    @1
    @0
    cF
    @18
    wfn
    #
    @2
    @1
    @18
    cR
    cbs
    cfv
    #
    cF
    wf
    @19
    cB
    cY
    cR
    cF
    @20
    coe1add.y
    coe1add.b
    @20
    eqid
    #
    ply1basf
    @18
    @20
    cF
    ffn
    syl
    3ad2ant2
    @2
    @0
    cG
    @18
    wfn
    #
    @1
    @2
    @18
    @20
    cG
    wf
    @22
    cB
    cY
    cR
    cG
    @20
    coe1add.y
    coe1add.b
    @21
    ply1basf
    @18
    @20
    cG
    ffn
    syl
    3ad2ant3
    cn0
    @18
    @5
    wf1o
    cn0
    @18
    @5
    wf
    @3
    va
    cn0
    c1o
    @5
    c0
    df1o2
    nn0ex
    0ex
    @5
    eqid
    #
    mapsnf1o3
    cn0
    @18
    @5
    f1of
    mp1i
    @3
    cn0
    c1o
    cmap
    ovexd
    #
    @24
    cn0
    cvv
    wcel
    @3
    nn0ex
    a1i
    @18
    inidm
    ofco
    eqtrd
    @3
    @4
    cB
    wcel
    #
    @11
    @6
    wceq
    @0
    cY
    crg
    wcel
    @1
    @2
    @25
    cY
    cR
    coe1add.y
    ply1ring
    cB
    c.pb
    cY
    cF
    cG
    coe1add.b
    coe1add.p
    ringacl
    syl3an1
    va
    @11
    cB
    cY
    cR
    @4
    @5
    @11
    eqid
    coe1add.b
    coe1add.y
    @23
    coe1fval2
    syl
    @3
    @12
    @7
    @13
    @8
    @9
    @1
    @0
    @12
    @7
    wceq
    @2
    va
    @12
    cB
    cY
    cR
    cF
    @5
    @12
    eqid
    coe1add.b
    coe1add.y
    @23
    coe1fval2
    3ad2ant2
    @2
    @0
    @13
    @8
    wceq
    @1
    va
    @13
    cB
    cY
    cR
    cG
    @5
    @13
    eqid
    coe1add.b
    coe1add.y
    @23
    coe1fval2
    3ad2ant3
    oveq12d
    3eqtr4d
end
