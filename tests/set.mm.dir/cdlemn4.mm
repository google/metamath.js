include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "wn.mm"
include "w3a.mm"
include "cid.mm"
include "cres.mm"
include "cop.mm"
include "co.mm"
include "ccom.mm"
include "csca.mm"
include "cfv.mm"
include "cplusg.mm"
include "ctendo.mm"
include "wceq.mm"
include "simp1.mm"
include "lhpocnel2.mm"
include "syl.mm"
include "simp2.mm"
include "ltrniotacl.mm"
include "syl3anc.mm"
include "eqid.mm"
include "tendoidcl.mm"
include "tendo0cl.mm"
include "dvhopvadd.mm"
include "syl122anc.mm"
include "ltrncom.mm"
include "cdlemn3.mm"
include "eqtrd.mm"
include "c0g.mm"
include "cedring.mm"
include "dvhsca.mm"
include "fveq2d.mm"
include "erng0g.mm"
include "oveq2d.mm"
include "cgrp.mm"
include "cbs.mm"
include "cdr.mm"
include "erngdv.mm"
include "drnggrp.mm"
include "eqeltrd.mm"
include "dvhbase.mm"
include "eleqtrrd.mm"
include "grprid.mm"
include "syl2anc.mm"
include "eqtr3d.mm"
include "opeq12d.mm"
include "eqtr2d.mm"

theorem cdlemn4
  let cA: class A
  let cB: class B
  let cP: class P
  let c.pl: class .+
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vh: setvar h
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let c.le: class .<_
  let cO: class O
  let cW: class W
  assume cdlemn4.b: |- B = ( Base ` K )
  assume cdlemn4.l: |- .<_ = ( le ` K )
  assume cdlemn4.a: |- A = ( Atoms ` K )
  assume cdlemn4.p: |- P = ( ( oc ` K ) ` W )
  assume cdlemn4.h: |- H = ( LHyp ` K )
  assume cdlemn4.t: |- T = ( ( LTrn ` K ) ` W )
  assume cdlemn4.o: |- O = ( h e. T |-> ( _I |` B ) )
  assume cdlemn4.u: |- U = ( ( DVecH ` K ) ` W )
  assume cdlemn4.f: |- F = ( iota_ h e. T ( h ` P ) = Q )
  assume cdlemn4.g: |- G = ( iota_ h e. T ( h ` P ) = R )
  assume cdlemn4.j: |- J = ( iota_ h e. T ( h ` Q ) = R )
  assume cdlemn4.s: |- .+ = ( +g ` U )

  disjoint .<_ h
  disjoint A h
  disjoint B h
  disjoint H h
  disjoint K h
  disjoint P h
  disjoint Q h
  disjoint R h
  disjoint T h
  disjoint W h
  assert |- ( ( ( K e. HL /\ W e. H ) /\ ( Q e. A /\ -. Q .<_ W ) /\ ( R e. A /\ -. R .<_ W ) ) -> <. G , ( _I |` T ) >. = ( <. F , ( _I |` T ) >. .+ <. J , O >. ) )

  proof
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    #
    cQ
    cA
    wcel
    cQ
    cW
    c.le
    wbr
    wn
    wa
    #
    cR
    cA
    wcel
    cR
    cW
    c.le
    wbr
    wn
    wa
    #
    w3a
    #
    cF
    cid
    cT
    cres
    #
    cop
    cJ
    cO
    cop
    c.pl
    co
    #
    cF
    cJ
    ccom
    #
    @4
    cO
    cU
    csca
    cfv
    #
    cplusg
    cfv
    #
    co
    #
    cop
    #
    cG
    @4
    cop
    @3
    @0
    cF
    cT
    wcel
    #
    @4
    cW
    cK
    ctendo
    cfv
    cfv
    #
    wcel
    #
    cJ
    cT
    wcel
    #
    cO
    @12
    wcel
    #
    @5
    @10
    wceq
    @0
    @1
    @2
    simp1
    #
    @3
    @0
    cP
    cA
    wcel
    cP
    cW
    c.le
    wbr
    wn
    wa
    #
    @1
    @11
    @16
    @3
    @0
    @17
    @16
    cA
    cP
    cH
    cK
    c.le
    cW
    cdlemn4.l
    cdlemn4.a
    cdlemn4.h
    cdlemn4.p
    lhpocnel2
    syl
    @0
    @1
    @2
    simp2
    cA
    cP
    cQ
    cT
    vh
    cF
    cH
    cK
    c.le
    cW
    cdlemn4.l
    cdlemn4.a
    cdlemn4.h
    cdlemn4.t
    cdlemn4.f
    ltrniotacl
    syl3anc
    #
    @3
    @0
    @13
    @16
    cT
    @12
    cH
    cK
    cW
    cdlemn4.h
    cdlemn4.t
    @12
    eqid
    #
    tendoidcl
    syl
    #
    cA
    cQ
    cR
    cT
    vh
    cJ
    cH
    cK
    c.le
    cW
    cdlemn4.l
    cdlemn4.a
    cdlemn4.h
    cdlemn4.t
    cdlemn4.j
    ltrniotacl
    #
    @3
    @0
    @15
    @16
    cB
    cT
    vh
    @12
    cH
    cK
    cO
    cW
    cdlemn4.b
    cdlemn4.h
    cdlemn4.t
    @19
    cdlemn4.o
    tendo0cl
    syl
    @7
    c.pl
    @8
    @4
    cO
    cT
    cU
    @12
    cF
    cJ
    cH
    cK
    cW
    cdlemn4.h
    cdlemn4.t
    @19
    cdlemn4.u
    @7
    eqid
    #
    cdlemn4.s
    @8
    eqid
    #
    dvhopvadd
    syl122anc
    @3
    @6
    cG
    @9
    @4
    @3
    @6
    cJ
    cF
    ccom
    #
    cG
    @3
    @0
    @11
    @14
    @6
    @24
    wceq
    @16
    @18
    @21
    cT
    cF
    cJ
    cH
    cK
    cW
    cdlemn4.h
    cdlemn4.t
    ltrncom
    syl3anc
    cA
    cP
    cQ
    cR
    cT
    vh
    cF
    cG
    cH
    cJ
    cK
    c.le
    cW
    cdlemn4.l
    cdlemn4.a
    cdlemn4.p
    cdlemn4.h
    cdlemn4.t
    cdlemn4.f
    cdlemn4.g
    cdlemn4.j
    cdlemn3
    eqtrd
    @3
    @4
    @7
    c0g
    cfv
    #
    @8
    co
    #
    @9
    @4
    @3
    @25
    cO
    @4
    @8
    @3
    @0
    @25
    cO
    wceq
    @16
    @0
    @25
    cW
    cK
    cedring
    cfv
    cfv
    #
    c0g
    cfv
    #
    cO
    @0
    @7
    @27
    c0g
    @27
    cU
    @7
    cH
    cK
    cW
    chlt
    cdlemn4.h
    @27
    eqid
    #
    cdlemn4.u
    @22
    dvhsca
    #
    fveq2d
    cB
    @27
    cT
    vh
    cH
    cK
    cO
    cW
    @28
    cdlemn4.b
    cdlemn4.h
    cdlemn4.t
    @29
    cdlemn4.o
    @28
    eqid
    erng0g
    eqtrd
    syl
    oveq2d
    @3
    @7
    cgrp
    wcel
    #
    @4
    @7
    cbs
    cfv
    #
    wcel
    @26
    @4
    wceq
    @3
    @0
    @31
    @16
    @0
    @7
    @27
    cgrp
    @30
    @0
    @27
    cdr
    wcel
    @27
    cgrp
    wcel
    @27
    cH
    cK
    cW
    cdlemn4.h
    @29
    erngdv
    @27
    drnggrp
    syl
    eqeltrd
    syl
    @3
    @4
    @12
    @32
    @20
    @3
    @0
    @32
    @12
    wceq
    @16
    @32
    cU
    @12
    @7
    cH
    cK
    cW
    chlt
    cdlemn4.h
    @19
    cdlemn4.u
    @22
    @32
    eqid
    #
    dvhbase
    syl
    eleqtrrd
    @32
    @8
    @7
    @4
    @25
    @33
    @23
    @25
    eqid
    grprid
    syl2anc
    eqtr3d
    opeq12d
    eqtr2d
end
