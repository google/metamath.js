include "cslw.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cqg.mm"
include "cqs.mm"
include "cpc.mm"
include "cexp.mm"
include "cdiv.mm"
include "cdvds.mm"
include "sylow3lem3.mm"
include "cmul.mm"
include "wbr.mm"
include "cress.mm"
include "cbs.mm"
include "csubg.mm"
include "wcel.mm"
include "cfn.mm"
include "slwsubg.mm"
include "syl.mm"
include "cnsg.mm"
include "eqid.mm"
include "nmznsg.mm"
include "nsgsubg.mm"
include "wceq.mm"
include "cgrp.mm"
include "nmzsubg.mm"
include "subgbas.mm"
include "wss.mm"
include "subgss.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "lagsubg.mm"
include "fveq2d.mm"
include "breqtrrd.mm"
include "cz.mm"
include "wi.mm"
include "cn.mm"
include "c0.mm"
include "wne.mm"
include "c0g.mm"
include "subg0cl.mm"
include "ne0i.mm"
include "wb.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "nnzd.mm"
include "cn0.mm"
include "hashcl.mm"
include "nn0zd.mm"
include "cpw.mm"
include "pwfi.mm"
include "sylib.mm"
include "wer.mm"
include "eqger.mm"
include "qsss.mm"
include "dvdscmul.mm"
include "syl3anc.mm"
include "mpd.mm"
include "nn0cnd.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcan1d.mm"
include "lagsubg2.mm"
include "eqtrd.mm"
include "cc0.mm"
include "dvdsval2.mm"
include "mpbid.mm"
include "dvdsmulcr.mm"
include "syl112anc.mm"
include "slwhash.mm"
include "oveq2d.mm"
include "breqtrd.mm"
include "eqbrtrd.mm"

theorem sylow3lem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let cP: class P
  let c.pl: class .+
  let c.po: class .(+)
  let cG: class G
  let cH: class H
  let cK: class K
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vv: setvar v
  let vw: setvar w
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  let vk: setvar k
  assume sylow3.x: |- X = ( Base ` G )
  assume sylow3.g: |- ( ph -> G e. Grp )
  assume sylow3.xf: |- ( ph -> X e. Fin )
  assume sylow3.p: |- ( ph -> P e. Prime )
  assume sylow3lem1.a: |- .+ = ( +g ` G )
  assume sylow3lem1.d: |- .- = ( -g ` G )
  assume sylow3lem1.m: |- .(+) = ( x e. X , y e. ( P pSyl G ) |-> ran ( z e. y |-> ( ( x .+ z ) .- x ) ) )
  assume sylow3lem2.k: |- ( ph -> K e. ( P pSyl G ) )
  assume sylow3lem2.h: |- H = { u e. X | ( u .(+) K ) = K }
  assume sylow3lem2.n: |- N = { x e. X | A. y e. X ( ( x .+ y ) e. K <-> ( y .+ x ) e. K ) }

  disjoint u x
  disjoint u y
  disjoint u z
  disjoint .- u
  disjoint x y
  disjoint x z
  disjoint .- x
  disjoint y z
  disjoint .- y
  disjoint .- z
  disjoint .(+) u
  disjoint .(+) x
  disjoint .(+) y
  disjoint .(+) z
  disjoint H x
  disjoint H y
  disjoint K u
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint N u
  disjoint N z
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint G u
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint ph u
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .+ u
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint P u
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint a b
  disjoint a c
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint .- a
  disjoint b c
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint .- b
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint .- c
  disjoint u v
  disjoint u w
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint .- v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .- w
  disjoint a g
  disjoint a h
  disjoint a s
  disjoint .(+) a
  disjoint b g
  disjoint b h
  disjoint b s
  disjoint .(+) b
  disjoint c g
  disjoint c h
  disjoint c s
  disjoint .(+) c
  disjoint g h
  disjoint g s
  disjoint g u
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint .(+) g
  disjoint h s
  disjoint h u
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint .(+) h
  disjoint s u
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint .(+) s
  disjoint .(+) w
  disjoint H g
  disjoint g v
  disjoint K g
  disjoint h v
  disjoint K h
  disjoint s v
  disjoint K s
  disjoint K v
  disjoint K w
  disjoint g k
  disjoint N g
  disjoint k u
  disjoint k w
  disjoint k z
  disjoint N k
  disjoint N w
  disjoint a k
  disjoint X a
  disjoint b k
  disjoint X b
  disjoint c k
  disjoint X c
  disjoint X g
  disjoint h k
  disjoint X h
  disjoint k x
  disjoint k y
  disjoint X k
  disjoint X w
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G g
  disjoint G h
  disjoint k s
  disjoint G k
  disjoint G s
  disjoint G w
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint g ph
  disjoint h ph
  disjoint k ph
  disjoint ph s
  disjoint ph w
  disjoint .+ a
  disjoint .+ b
  disjoint .+ c
  disjoint .+ g
  disjoint .+ v
  disjoint .+ w
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P g
  disjoint P h
  disjoint P k
  disjoint P s
  disjoint P w
  assert |- ( ph -> ( # ` ( P pSyl G ) ) || ( ( # ` X ) / ( P ^ ( P pCnt ( # ` X ) ) ) ) )

  proof
    wph
    cP
    cG
    cslw
    co
    #
    chash
    cfv
    cX
    cG
    cN
    cqg
    co
    #
    cqs
    #
    chash
    cfv
    #
    cX
    chash
    cfv
    #
    cP
    cP
    @4
    cpc
    co
    cexp
    co
    #
    cdiv
    co
    #
    cdvds
    wph
    vx
    vy
    vz
    vu
    cP
    c.pl
    c.po
    cG
    cH
    cK
    c.mi
    cN
    cX
    sylow3.x
    sylow3.g
    sylow3.xf
    sylow3.p
    sylow3lem1.a
    sylow3lem1.d
    sylow3lem1.m
    sylow3lem2.k
    sylow3lem2.h
    sylow3lem2.n
    sylow3lem3
    wph
    @3
    @4
    cK
    chash
    cfv
    #
    cdiv
    co
    #
    @6
    cdvds
    wph
    @3
    @7
    cmul
    co
    #
    @8
    @7
    cmul
    co
    #
    cdvds
    wbr
    #
    @3
    @8
    cdvds
    wbr
    #
    wph
    @9
    @3
    cN
    chash
    cfv
    #
    cmul
    co
    #
    @10
    cdvds
    wph
    @7
    @13
    cdvds
    wbr
    #
    @9
    @14
    cdvds
    wbr
    #
    wph
    @7
    cG
    cN
    cress
    co
    #
    cbs
    cfv
    #
    chash
    cfv
    #
    @13
    cdvds
    wph
    cK
    @17
    csubg
    cfv
    wcel
    #
    @18
    cfn
    wcel
    @7
    @19
    cdvds
    wbr
    wph
    cK
    cG
    csubg
    cfv
    #
    wcel
    #
    @20
    wph
    cK
    @0
    wcel
    @22
    sylow3lem2.k
    cP
    cG
    cK
    slwsubg
    syl
    #
    @22
    cK
    @17
    cnsg
    cfv
    wcel
    @20
    vx
    vy
    c.pl
    cK
    cG
    @17
    cN
    cX
    sylow3lem2.n
    sylow3.x
    sylow3lem1.a
    @17
    eqid
    #
    nmznsg
    cK
    @17
    nsgsubg
    syl
    syl
    wph
    cN
    @18
    cfn
    wph
    cN
    @21
    wcel
    #
    cN
    @18
    wceq
    wph
    cG
    cgrp
    wcel
    @25
    sylow3.g
    vx
    vy
    c.pl
    cK
    cG
    cN
    cX
    sylow3lem2.n
    sylow3.x
    sylow3lem1.a
    nmzsubg
    syl
    #
    cN
    cG
    @17
    @24
    subgbas
    syl
    #
    wph
    cX
    cfn
    wcel
    #
    cN
    cX
    wss
    #
    cN
    cfn
    wcel
    #
    sylow3.xf
    wph
    @25
    @29
    @26
    cX
    cN
    cG
    sylow3.x
    subgss
    syl
    cX
    cN
    ssfi
    syl2anc
    #
    eqeltrrd
    @17
    @18
    cK
    @18
    eqid
    lagsubg
    syl2anc
    wph
    cN
    @18
    chash
    @27
    fveq2d
    breqtrrd
    wph
    @7
    cz
    wcel
    #
    @13
    cz
    wcel
    @3
    cz
    wcel
    #
    @15
    @16
    wi
    wph
    @7
    wph
    @7
    cn
    wcel
    #
    cK
    c0
    wne
    #
    wph
    cG
    c0g
    cfv
    #
    cK
    wcel
    #
    @35
    wph
    @22
    @37
    @23
    cK
    cG
    @36
    @36
    eqid
    subg0cl
    syl
    cK
    @36
    ne0i
    syl
    wph
    cK
    cfn
    wcel
    #
    @34
    @35
    wb
    wph
    @28
    cK
    cX
    wss
    #
    @38
    sylow3.xf
    wph
    @22
    @39
    @23
    cX
    cK
    cG
    sylow3.x
    subgss
    syl
    cX
    cK
    ssfi
    syl2anc
    cK
    hashnncl
    syl
    mpbird
    #
    nnzd
    #
    wph
    @13
    wph
    @30
    @13
    cn0
    wcel
    @31
    cN
    hashcl
    syl
    nn0zd
    wph
    @3
    wph
    @2
    cfn
    wcel
    #
    @3
    cn0
    wcel
    wph
    cX
    cpw
    #
    cfn
    wcel
    #
    @2
    @43
    wss
    @42
    wph
    @28
    @44
    sylow3.xf
    cX
    pwfi
    sylib
    wph
    cX
    @1
    wph
    @25
    cX
    @1
    wer
    @26
    @1
    cG
    cX
    cN
    sylow3.x
    @1
    eqid
    #
    eqger
    syl
    qsss
    @43
    @2
    ssfi
    syl2anc
    @2
    hashcl
    syl
    nn0zd
    #
    @3
    @7
    @13
    dvdscmul
    syl3anc
    mpd
    wph
    @10
    @4
    @14
    wph
    @4
    @7
    wph
    @4
    wph
    @28
    @4
    cn0
    wcel
    sylow3.xf
    cX
    hashcl
    syl
    #
    nn0cnd
    wph
    @7
    @40
    nncnd
    wph
    @7
    @40
    nnne0d
    #
    divcan1d
    wph
    @1
    cG
    cX
    cN
    sylow3.x
    @45
    @26
    sylow3.xf
    lagsubg2
    eqtrd
    breqtrrd
    wph
    @33
    @8
    cz
    wcel
    #
    @32
    @7
    cc0
    wne
    #
    @11
    @12
    wb
    @46
    wph
    @7
    @4
    cdvds
    wbr
    #
    @49
    wph
    @22
    @28
    @51
    @23
    sylow3.xf
    cG
    cX
    cK
    sylow3.x
    lagsubg
    syl2anc
    wph
    @32
    @50
    @4
    cz
    wcel
    @51
    @49
    wb
    @41
    @48
    wph
    @4
    @47
    nn0zd
    @7
    @4
    dvdsval2
    syl3anc
    mpbid
    @41
    @48
    @7
    @3
    @8
    dvdsmulcr
    syl112anc
    mpbid
    wph
    @7
    @5
    @4
    cdiv
    wph
    cP
    cG
    cK
    cX
    sylow3.x
    sylow3.xf
    sylow3lem2.k
    slwhash
    oveq2d
    breqtrd
    eqbrtrd
end
