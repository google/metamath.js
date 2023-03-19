include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "deg1addle.mm"
include "clt.mm"
include "wn.mm"
include "cxr.mm"
include "wcel.mm"
include "wb.mm"
include "deg1xrcl.mm"
include "syl.mm"
include "xrltnle.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "iffalsed.mm"
include "breqtrd.mm"
include "cn0.mm"
include "cco1.mm"
include "c0g.mm"
include "wne.mm"
include "crg.mm"
include "ply1ring.mm"
include "ringacl.mm"
include "syl3anc.mm"
include "cmnf.mm"
include "nltmnf.mm"
include "wa.mm"
include "adantr.mm"
include "fveq2.mm"
include "eqid.mm"
include "deg1z.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "necon3bd.mm"
include "mpd.mm"
include "deg1nn0cl.mm"
include "cplusg.mm"
include "coe1addfv.mm"
include "syl31anc.mm"
include "deg1lt.mm"
include "oveq2d.mm"
include "cgrp.mm"
include "cbs.mm"
include "ringgrp.mm"
include "wf.mm"
include "coe1f.mm"
include "ffvelrnd.mm"
include "grprid.mm"
include "3eqtrd.mm"
include "deg1ldg.mm"
include "eqnetrd.mm"
include "deg1ge.mm"
include "xrletri3.mm"
include "mpbir2and.mm"

theorem deg1add
  let wph: wff ph
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let cR: class R
  let cF: class F
  let cG: class G
  let cY: class Y
  assume deg1addle.y: |- Y = ( Poly1 ` R )
  assume deg1addle.d: |- D = ( deg1 ` R )
  assume deg1addle.r: |- ( ph -> R e. Ring )
  assume deg1addle.b: |- B = ( Base ` Y )
  assume deg1addle.p: |- .+ = ( +g ` Y )
  assume deg1addle.f: |- ( ph -> F e. B )
  assume deg1addle.g: |- ( ph -> G e. B )
  assume deg1add.l: |- ( ph -> ( D ` G ) < ( D ` F ) )


  assert |- ( ph -> ( D ` ( F .+ G ) ) = ( D ` F ) )

  proof
    wph
    cF
    cG
    c.pl
    co
    #
    cD
    cfv
    #
    cF
    cD
    cfv
    #
    wceq
    #
    @1
    @2
    cle
    wbr
    #
    @2
    @1
    cle
    wbr
    #
    wph
    @1
    @2
    cG
    cD
    cfv
    #
    cle
    wbr
    #
    @6
    @2
    cif
    @2
    cle
    wph
    cB
    cD
    c.pl
    cR
    cF
    cG
    cY
    deg1addle.y
    deg1addle.d
    deg1addle.r
    deg1addle.b
    deg1addle.p
    deg1addle.f
    deg1addle.g
    deg1addle
    wph
    @7
    @6
    @2
    wph
    @6
    @2
    clt
    wbr
    #
    @7
    wn
    #
    deg1add.l
    wph
    @6
    cxr
    wcel
    #
    @2
    cxr
    wcel
    #
    @8
    @9
    wb
    wph
    cG
    cB
    wcel
    #
    @10
    deg1addle.g
    cB
    cD
    cY
    cR
    cG
    deg1addle.d
    deg1addle.y
    deg1addle.b
    deg1xrcl
    syl
    #
    wph
    cF
    cB
    wcel
    #
    @11
    deg1addle.f
    cB
    cD
    cY
    cR
    cF
    deg1addle.d
    deg1addle.y
    deg1addle.b
    deg1xrcl
    syl
    #
    @6
    @2
    xrltnle
    syl2anc
    mpbid
    iffalsed
    breqtrd
    wph
    @0
    cB
    wcel
    #
    @2
    cn0
    wcel
    #
    @2
    @0
    cco1
    cfv
    #
    cfv
    #
    cR
    c0g
    cfv
    #
    wne
    @5
    wph
    cY
    crg
    wcel
    #
    @14
    @12
    @16
    wph
    cR
    crg
    wcel
    #
    @21
    deg1addle.r
    cY
    cR
    deg1addle.y
    ply1ring
    syl
    deg1addle.f
    deg1addle.g
    cB
    c.pl
    cY
    cF
    cG
    deg1addle.b
    deg1addle.p
    ringacl
    syl3anc
    #
    wph
    @22
    @14
    cF
    cY
    c0g
    cfv
    #
    wne
    #
    @17
    deg1addle.r
    deg1addle.f
    wph
    @6
    cmnf
    clt
    wbr
    #
    wn
    #
    @25
    wph
    @10
    @27
    @13
    @6
    nltmnf
    syl
    wph
    @26
    cF
    @24
    wph
    cF
    @24
    wceq
    #
    @26
    wph
    @28
    wa
    @6
    @2
    cmnf
    clt
    wph
    @8
    @28
    deg1add.l
    adantr
    @28
    wph
    @2
    @24
    cD
    cfv
    #
    cmnf
    cF
    @24
    cD
    fveq2
    wph
    @22
    @29
    cmnf
    wceq
    deg1addle.r
    cD
    cY
    cR
    @24
    deg1addle.d
    deg1addle.y
    @24
    eqid
    #
    deg1z
    syl
    sylan9eqr
    breqtrd
    ex
    necon3bd
    mpd
    #
    cB
    cD
    cY
    cR
    cF
    @24
    deg1addle.d
    deg1addle.y
    @30
    deg1addle.b
    deg1nn0cl
    syl3anc
    #
    wph
    @19
    @2
    cF
    cco1
    cfv
    #
    cfv
    #
    @20
    wph
    @19
    @34
    @2
    cG
    cco1
    cfv
    #
    cfv
    #
    cR
    cplusg
    cfv
    #
    co
    #
    @34
    @20
    @37
    co
    #
    @34
    wph
    @22
    @14
    @12
    @17
    @19
    @38
    wceq
    deg1addle.r
    deg1addle.f
    deg1addle.g
    @32
    cB
    @37
    c.pl
    cR
    cF
    cG
    @2
    cY
    deg1addle.y
    deg1addle.b
    deg1addle.p
    @37
    eqid
    #
    coe1addfv
    syl31anc
    wph
    @36
    @20
    @34
    @37
    wph
    @12
    @17
    @8
    @36
    @20
    wceq
    deg1addle.g
    @32
    deg1add.l
    @35
    cB
    cD
    cY
    cR
    cG
    @2
    @20
    deg1addle.d
    deg1addle.y
    deg1addle.b
    @20
    eqid
    #
    @35
    eqid
    deg1lt
    syl3anc
    oveq2d
    wph
    cR
    cgrp
    wcel
    #
    @34
    cR
    cbs
    cfv
    #
    wcel
    @39
    @34
    wceq
    wph
    @22
    @42
    deg1addle.r
    cR
    ringgrp
    syl
    wph
    cn0
    @43
    @2
    @33
    wph
    @14
    cn0
    @43
    @33
    wf
    deg1addle.f
    @33
    cB
    cY
    cR
    cF
    @43
    @33
    eqid
    #
    deg1addle.b
    deg1addle.y
    @43
    eqid
    #
    coe1f
    syl
    @32
    ffvelrnd
    @43
    @37
    cR
    @34
    @20
    @45
    @40
    @41
    grprid
    syl2anc
    3eqtrd
    wph
    @22
    @14
    @25
    @34
    @20
    wne
    deg1addle.r
    deg1addle.f
    @31
    @33
    cB
    cD
    cY
    cR
    cF
    @20
    @24
    deg1addle.d
    deg1addle.y
    @30
    deg1addle.b
    @41
    @44
    deg1ldg
    syl3anc
    eqnetrd
    @18
    cB
    cD
    cY
    cR
    @0
    @2
    @20
    deg1addle.d
    deg1addle.y
    deg1addle.b
    @41
    @18
    eqid
    deg1ge
    syl3anc
    wph
    @1
    cxr
    wcel
    #
    @11
    @3
    @4
    @5
    wa
    wb
    wph
    @16
    @46
    @23
    cB
    cD
    cY
    cR
    @0
    deg1addle.d
    deg1addle.y
    deg1addle.b
    deg1xrcl
    syl
    @15
    @1
    @2
    xrletri3
    syl2anc
    mpbir2and
end
