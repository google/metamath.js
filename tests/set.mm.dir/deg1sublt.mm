include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wn.mm"
include "clt.mm"
include "wbr.mm"
include "wo.mm"
include "cco1.mm"
include "c0g.mm"
include "eqid.mm"
include "cgrp.mm"
include "wcel.mm"
include "crg.mm"
include "ply1ring.mm"
include "ringgrp.mm"
include "3syl.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "csg.mm"
include "cn0.mm"
include "coe1subfv.mm"
include "syl31anc.mm"
include "oveq1d.mm"
include "cbs.mm"
include "syl.mm"
include "wf.mm"
include "coe1f.mm"
include "ffvelrnd.mm"
include "grpsubid.mm"
include "syl2anc.mm"
include "3eqtrd.mm"
include "deg1ldgn.mm"
include "neneqd.mm"
include "cle.mm"
include "cif.mm"
include "cxr.mm"
include "deg1xrcl.mm"
include "ifcld.mm"
include "nn0red.mm"
include "rexrd.mm"
include "deg1suble.mm"
include "wa.mm"
include "wb.mm"
include "xrmaxle.mm"
include "mpbir2and.mm"
include "xrletrd.mm"
include "xrleloe.mm"
include "mpbid.mm"
include "orel2.mm"
include "sylc.mm"

theorem deg1sublt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cR: class R
  let cF: class F
  let cG: class G
  let cL: class L
  let c.mi: class .-
  assume deg1sublt.d: |- D = ( deg1 ` R )
  assume deg1sublt.p: |- P = ( Poly1 ` R )
  assume deg1sublt.b: |- B = ( Base ` P )
  assume deg1sublt.m: |- .- = ( -g ` P )
  assume deg1sublt.l: |- ( ph -> L e. NN0 )
  assume deg1sublt.r: |- ( ph -> R e. Ring )
  assume deg1sublt.fb: |- ( ph -> F e. B )
  assume deg1sublt.fd: |- ( ph -> ( D ` F ) <_ L )
  assume deg1sublt.gb: |- ( ph -> G e. B )
  assume deg1sublt.gd: |- ( ph -> ( D ` G ) <_ L )
  assume deg1sublt.a: |- A = ( coe1 ` F )
  assume deg1sublt.c: |- C = ( coe1 ` G )
  assume deg1sublt.eq: |- ( ph -> ( ( coe1 ` F ) ` L ) = ( ( coe1 ` G ) ` L ) )


  assert |- ( ph -> ( D ` ( F .- G ) ) < L )

  proof
    wph
    cF
    cG
    c.mi
    co
    #
    cD
    cfv
    #
    cL
    wceq
    #
    wn
    @1
    cL
    clt
    wbr
    #
    @2
    wo
    #
    @3
    wph
    @1
    cL
    wph
    @0
    cco1
    cfv
    #
    cB
    cD
    cP
    cR
    @0
    cL
    cR
    c0g
    cfv
    #
    cP
    c0g
    cfv
    #
    deg1sublt.d
    deg1sublt.p
    @7
    eqid
    deg1sublt.b
    @6
    eqid
    #
    @5
    eqid
    deg1sublt.r
    wph
    cP
    cgrp
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
    @0
    cB
    wcel
    #
    wph
    cR
    crg
    wcel
    #
    cP
    crg
    wcel
    @9
    deg1sublt.r
    cP
    cR
    deg1sublt.p
    ply1ring
    cP
    ringgrp
    3syl
    deg1sublt.fb
    deg1sublt.gb
    cB
    cP
    c.mi
    cF
    cG
    deg1sublt.b
    deg1sublt.m
    grpsubcl
    syl3anc
    #
    deg1sublt.l
    wph
    cL
    @5
    cfv
    #
    cL
    cF
    cco1
    cfv
    cfv
    #
    cL
    cG
    cco1
    cfv
    #
    cfv
    #
    cR
    csg
    cfv
    #
    co
    #
    @18
    @18
    @19
    co
    #
    @6
    wph
    @13
    @10
    @11
    cL
    cn0
    wcel
    @15
    @20
    wceq
    deg1sublt.r
    deg1sublt.fb
    deg1sublt.gb
    deg1sublt.l
    cB
    cR
    cF
    cG
    c.mi
    @19
    cL
    cP
    deg1sublt.p
    deg1sublt.b
    deg1sublt.m
    @19
    eqid
    #
    coe1subfv
    syl31anc
    wph
    @16
    @18
    @18
    @19
    deg1sublt.eq
    oveq1d
    wph
    cR
    cgrp
    wcel
    #
    @18
    cR
    cbs
    cfv
    #
    wcel
    @21
    @6
    wceq
    wph
    @13
    @23
    deg1sublt.r
    cR
    ringgrp
    syl
    wph
    cn0
    @24
    cL
    @17
    wph
    @11
    cn0
    @24
    @17
    wf
    deg1sublt.gb
    @17
    cB
    cP
    cR
    cG
    @24
    @17
    eqid
    deg1sublt.b
    deg1sublt.p
    @24
    eqid
    #
    coe1f
    syl
    deg1sublt.l
    ffvelrnd
    @24
    cR
    @19
    @18
    @6
    @25
    @8
    @22
    grpsubid
    syl2anc
    3eqtrd
    deg1ldgn
    neneqd
    wph
    @1
    cL
    cle
    wbr
    #
    @4
    wph
    @1
    cF
    cD
    cfv
    #
    cG
    cD
    cfv
    #
    cle
    wbr
    #
    @28
    @27
    cif
    #
    cL
    wph
    @12
    @1
    cxr
    wcel
    #
    @14
    cB
    cD
    cP
    cR
    @0
    deg1sublt.d
    deg1sublt.p
    deg1sublt.b
    deg1xrcl
    syl
    #
    wph
    @29
    @28
    @27
    cxr
    wph
    @11
    @28
    cxr
    wcel
    #
    deg1sublt.gb
    cB
    cD
    cP
    cR
    cG
    deg1sublt.d
    deg1sublt.p
    deg1sublt.b
    deg1xrcl
    syl
    #
    wph
    @10
    @27
    cxr
    wcel
    #
    deg1sublt.fb
    cB
    cD
    cP
    cR
    cF
    deg1sublt.d
    deg1sublt.p
    deg1sublt.b
    deg1xrcl
    syl
    #
    ifcld
    wph
    cL
    wph
    cL
    deg1sublt.l
    nn0red
    rexrd
    #
    wph
    cB
    cD
    cR
    cF
    cG
    c.mi
    cP
    deg1sublt.p
    deg1sublt.d
    deg1sublt.r
    deg1sublt.b
    deg1sublt.m
    deg1sublt.fb
    deg1sublt.gb
    deg1suble
    wph
    @30
    cL
    cle
    wbr
    #
    @27
    cL
    cle
    wbr
    #
    @28
    cL
    cle
    wbr
    #
    deg1sublt.fd
    deg1sublt.gd
    wph
    @35
    @33
    cL
    cxr
    wcel
    #
    @38
    @39
    @40
    wa
    wb
    @36
    @34
    @37
    @27
    @28
    cL
    xrmaxle
    syl3anc
    mpbir2and
    xrletrd
    wph
    @31
    @41
    @26
    @4
    wb
    @32
    @37
    @1
    cL
    xrleloe
    syl2anc
    mpbid
    @2
    @3
    orel2
    sylc
end
