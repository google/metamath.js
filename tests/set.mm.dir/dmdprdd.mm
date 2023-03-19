include "cdprd.mm"
include "cdm.mm"
include "wbr.mm"
include "cgrp.mm"
include "wcel.mm"
include "csubg.mm"
include "cfv.mm"
include "wf.mm"
include "cv.mm"
include "wss.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "cima.mm"
include "cuni.mm"
include "cin.mm"
include "wceq.mm"
include "wa.mm"
include "wne.mm"
include "eldifsn.mm"
include "necom.mm"
include "anbi2i.mm"
include "bitri.mm"
include "3exp2.mm"
include "imp4b.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "ffvelrnda.mm"
include "subg0cl.mm"
include "syl.mm"
include "cbs.mm"
include "cmre.mm"
include "cacs.mm"
include "adantr.mm"
include "eqid.mm"
include "subgacs.mm"
include "acsmre.mm"
include "3syl.mm"
include "cpw.mm"
include "crn.mm"
include "imassrn.mm"
include "frn.mm"
include "syl5ss.mm"
include "mresspw.mm"
include "sstrd.mm"
include "sspwuni.mm"
include "sylib.mm"
include "mrccl.mm"
include "syl2anc.mm"
include "elind.mm"
include "snssd.mm"
include "eqssd.mm"
include "jca.mm"
include "ralrimiva.mm"
include "w3a.mm"
include "wb.mm"
include "fdm.mm"
include "dmdprd.mm"
include "mpbir3and.mm"

theorem dmdprdd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cG: class G
  let cI: class I
  let cK: class K
  let cV: class V
  let c.0: class .0.
  let cZ: class Z
  let vg: setvar g
  let vh: setvar h
  let vf: setvar f
  let vi: setvar i
  let vs: setvar s
  assume dmdprd.z: |- Z = ( Cntz ` G )
  assume dmdprd.0: |- .0. = ( 0g ` G )
  assume dmdprd.k: |- K = ( mrCls ` ( SubGrp ` G ) )
  assume dmdprdd.1: |- ( ph -> G e. Grp )
  assume dmdprdd.2: |- ( ph -> I e. V )
  assume dmdprdd.3: |- ( ph -> S : I --> ( SubGrp ` G ) )
  assume dmdprdd.4: |- ( ( ph /\ ( x e. I /\ y e. I /\ x =/= y ) ) -> ( S ` x ) C_ ( Z ` ( S ` y ) ) )
  assume dmdprdd.5: |- ( ( ph /\ x e. I ) -> ( ( S ` x ) i^i ( K ` U. ( S " ( I \ { x } ) ) ) ) C_ { .0. } )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint I x
  disjoint I y
  disjoint ph x
  disjoint ph y
  disjoint S x
  disjoint S y
  disjoint V x
  disjoint V y
  disjoint g h
  disjoint .0. g
  disjoint .0. h
  disjoint f g
  disjoint f h
  disjoint f i
  disjoint f s
  disjoint f x
  disjoint f y
  disjoint G f
  disjoint g i
  disjoint g s
  disjoint g x
  disjoint g y
  disjoint G g
  disjoint h i
  disjoint h s
  disjoint h x
  disjoint h y
  disjoint G h
  disjoint i s
  disjoint i x
  disjoint i y
  disjoint G i
  disjoint s x
  disjoint s y
  disjoint G s
  disjoint I h
  disjoint K g
  disjoint K h
  disjoint Z g
  disjoint Z h
  disjoint S g
  disjoint S h
  disjoint V h
  assert |- ( ph -> G dom DProd S )

  proof
    wph
    cG
    cS
    cdprd
    cdm
    wbr
    #
    cG
    cgrp
    wcel
    #
    cI
    cG
    csubg
    cfv
    #
    cS
    wf
    #
    vx
    cv
    #
    cS
    cfv
    #
    vy
    cv
    #
    cS
    cfv
    cZ
    cfv
    wss
    #
    vy
    cI
    @4
    csn
    cdif
    #
    wral
    #
    @5
    cS
    @8
    cima
    #
    cuni
    #
    cK
    cfv
    #
    cin
    #
    c.0
    csn
    #
    wceq
    #
    wa
    #
    vx
    cI
    wral
    #
    dmdprdd.1
    dmdprdd.3
    wph
    @16
    vx
    cI
    wph
    @4
    cI
    wcel
    #
    wa
    #
    @9
    @15
    @19
    @7
    vy
    @8
    @6
    @8
    wcel
    #
    @6
    cI
    wcel
    #
    @4
    @6
    wne
    #
    wa
    #
    @19
    @7
    @20
    @21
    @6
    @4
    wne
    #
    wa
    @23
    @6
    cI
    @4
    eldifsn
    @24
    @22
    @21
    @6
    @4
    necom
    anbi2i
    bitri
    wph
    @18
    @21
    @22
    @7
    wph
    @18
    @21
    @22
    @7
    dmdprdd.4
    3exp2
    imp4b
    syl5bi
    ralrimiv
    @19
    @13
    @14
    dmdprdd.5
    @19
    c.0
    @13
    @19
    @5
    @12
    c.0
    @19
    @5
    @2
    wcel
    c.0
    @5
    wcel
    wph
    cI
    @2
    @4
    cS
    dmdprdd.3
    ffvelrnda
    @5
    cG
    c.0
    dmdprd.0
    subg0cl
    syl
    @19
    @12
    @2
    wcel
    #
    c.0
    @12
    wcel
    @19
    @2
    cG
    cbs
    cfv
    #
    cmre
    cfv
    wcel
    #
    @11
    @26
    wss
    #
    @25
    @19
    @1
    @2
    @26
    cacs
    cfv
    wcel
    @27
    wph
    @1
    @18
    dmdprdd.1
    adantr
    @26
    cG
    @26
    eqid
    subgacs
    @2
    @26
    acsmre
    3syl
    #
    @19
    @10
    @26
    cpw
    #
    wss
    @28
    @19
    @10
    @2
    @30
    @19
    @10
    cS
    crn
    #
    @2
    cS
    @8
    imassrn
    wph
    @31
    @2
    wss
    #
    @18
    wph
    @3
    @32
    dmdprdd.3
    cI
    @2
    cS
    frn
    syl
    adantr
    syl5ss
    @19
    @27
    @2
    @30
    wss
    @29
    @2
    @26
    mresspw
    syl
    sstrd
    @10
    @26
    sspwuni
    sylib
    @2
    @11
    cK
    @26
    dmdprd.k
    mrccl
    syl2anc
    @12
    cG
    c.0
    dmdprd.0
    subg0cl
    syl
    elind
    snssd
    eqssd
    jca
    ralrimiva
    wph
    cI
    cV
    wcel
    cS
    cdm
    cI
    wceq
    #
    @0
    @1
    @3
    @17
    w3a
    wb
    dmdprdd.2
    wph
    @3
    @33
    dmdprdd.3
    cI
    @2
    cS
    fdm
    syl
    vx
    vy
    cS
    cG
    cI
    cK
    cV
    c.0
    cZ
    dmdprd.z
    dmdprd.0
    dmdprd.k
    dmdprd
    syl2anc
    mpbir3and
end
