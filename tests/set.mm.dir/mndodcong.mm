include "cmnd.mm"
include "wcel.mm"
include "wa.mm"
include "cn0.mm"
include "cfv.mm"
include "cn.mm"
include "w3a.mm"
include "cmo.mm"
include "co.mm"
include "wceq.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "oveq1.mm"
include "simp2l.mm"
include "nn0zd.mm"
include "simp3.mm"
include "zmodcld.mm"
include "adantr.mm"
include "nn0red.mm"
include "simp2r.mm"
include "simp1l.mm"
include "simp1r.mm"
include "clt.mm"
include "cr.mm"
include "crp.mm"
include "nnrpd.mm"
include "modlt.mm"
include "syl2anc.mm"
include "simpr.mm"
include "mndodconglem.mm"
include "cle.mm"
include "eqcomd.mm"
include "lecasei.mm"
include "ex.mm"
include "impbid2.mm"
include "cz.mm"
include "wb.mm"
include "moddvds.mm"
include "syl3anc.mm"
include "odmodnn0.mm"
include "syl31anc.mm"
include "eqeq12d.mm"
include "3bitr3d.mm"

theorem mndodcong
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cM: class M
  let cN: class N
  let cO: class O
  let cX: class X
  let c.0: class .0.
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x
  assume odcl.1: |- X = ( Base ` G )
  assume odcl.2: |- O = ( od ` G )
  assume odid.3: |- .x. = ( .g ` G )
  assume odid.4: |- .0. = ( 0g ` G )


  assert |- ( ( ( G e. Mnd /\ A e. X ) /\ ( M e. NN0 /\ N e. NN0 ) /\ ( O ` A ) e. NN ) -> ( ( O ` A ) || ( M - N ) <-> ( M .x. A ) = ( N .x. A ) ) )

  proof
    cG
    cmnd
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cM
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    cA
    cO
    cfv
    #
    cn
    wcel
    #
    w3a
    #
    cM
    @6
    cmo
    co
    #
    cN
    @6
    cmo
    co
    #
    wceq
    #
    @9
    cA
    c.x
    co
    #
    @10
    cA
    c.x
    co
    #
    wceq
    #
    @6
    cM
    cN
    cmin
    co
    cdvds
    wbr
    #
    cM
    cA
    c.x
    co
    #
    cN
    cA
    c.x
    co
    #
    wceq
    @8
    @11
    @14
    @9
    @10
    cA
    c.x
    oveq1
    @8
    @14
    @11
    @8
    @14
    wa
    #
    @11
    @9
    @10
    @18
    @9
    @8
    @9
    cn0
    wcel
    @14
    @8
    cM
    @6
    @8
    cM
    @2
    @3
    @4
    @7
    simp2l
    #
    nn0zd
    #
    @2
    @5
    @7
    simp3
    #
    zmodcld
    adantr
    #
    nn0red
    @18
    @10
    @8
    @10
    cn0
    wcel
    @14
    @8
    cN
    @6
    @8
    cN
    @2
    @3
    @4
    @7
    simp2r
    #
    nn0zd
    #
    @21
    zmodcld
    adantr
    #
    nn0red
    @18
    cA
    c.x
    cG
    @9
    @10
    cO
    cX
    c.0
    odcl.1
    odcl.2
    odid.3
    odid.4
    @8
    @0
    @14
    @0
    @1
    @5
    @7
    simp1l
    #
    adantr
    #
    @8
    @1
    @14
    @0
    @1
    @5
    @7
    simp1r
    #
    adantr
    #
    @8
    @7
    @14
    @21
    adantr
    #
    @22
    @25
    @8
    @9
    @6
    clt
    wbr
    #
    @14
    @8
    cM
    cr
    wcel
    @6
    crp
    wcel
    #
    @31
    @8
    cM
    @19
    nn0red
    @8
    @6
    @21
    nnrpd
    #
    cM
    @6
    modlt
    syl2anc
    adantr
    #
    @8
    @10
    @6
    clt
    wbr
    #
    @14
    @8
    cN
    cr
    wcel
    @32
    @35
    @8
    cN
    @23
    nn0red
    @33
    cN
    @6
    modlt
    syl2anc
    adantr
    #
    @8
    @14
    simpr
    #
    mndodconglem
    @18
    @10
    @9
    cle
    wbr
    wa
    @10
    @9
    @18
    cA
    c.x
    cG
    @10
    @9
    cO
    cX
    c.0
    odcl.1
    odcl.2
    odid.3
    odid.4
    @27
    @29
    @30
    @25
    @22
    @36
    @34
    @18
    @12
    @13
    @37
    eqcomd
    mndodconglem
    eqcomd
    lecasei
    ex
    impbid2
    @8
    @7
    cM
    cz
    wcel
    cN
    cz
    wcel
    @11
    @15
    wb
    @21
    @20
    @24
    cM
    cN
    @6
    moddvds
    syl3anc
    @8
    @12
    @16
    @13
    @17
    @8
    @0
    @1
    @3
    @7
    @12
    @16
    wceq
    @26
    @28
    @19
    @21
    cA
    c.x
    cG
    cM
    cO
    cX
    c.0
    odcl.1
    odcl.2
    odid.3
    odid.4
    odmodnn0
    syl31anc
    @8
    @0
    @1
    @4
    @7
    @13
    @17
    wceq
    @26
    @28
    @23
    @21
    cA
    c.x
    cG
    cN
    cO
    cX
    c.0
    odcl.1
    odcl.2
    odid.3
    odid.4
    odmodnn0
    syl31anc
    eqeq12d
    3bitr3d
end
