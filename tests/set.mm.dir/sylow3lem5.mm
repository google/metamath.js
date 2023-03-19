include "cslw.mm"
include "co.mm"
include "cv.mm"
include "cmpt.mm"
include "crn.mm"
include "cmpt2.mm"
include "cxp.mm"
include "cres.mm"
include "cress.mm"
include "cga.mm"
include "wss.mm"
include "wceq.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "slwsubg.mm"
include "syl.mm"
include "subgss.mm"
include "ssid.mm"
include "resmpt2.mm"
include "sylancl.mm"
include "syl6eqr.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "cbvmptv.mm"
include "oveq1.mm"
include "id.mm"
include "oveq12d.mm"
include "mpteq2dv.mm"
include "syl5eq.mm"
include "rneqd.mm"
include "mpteq1.mm"
include "cbvmpt2v.mm"
include "sylow3lem1.mm"
include "eqid.mm"
include "gasubg.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"

theorem sylow3lem5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cP: class P
  let c.pl: class .+
  let c.po: class .(+)
  let cG: class G
  let cK: class K
  let c.mi: class .-
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  let cH: class H
  let vk: setvar k
  let cN: class N
  assume sylow3.x: |- X = ( Base ` G )
  assume sylow3.g: |- ( ph -> G e. Grp )
  assume sylow3.xf: |- ( ph -> X e. Fin )
  assume sylow3.p: |- ( ph -> P e. Prime )
  assume sylow3lem5.a: |- .+ = ( +g ` G )
  assume sylow3lem5.d: |- .- = ( -g ` G )
  assume sylow3lem5.k: |- ( ph -> K e. ( P pSyl G ) )
  assume sylow3lem5.m: |- .(+) = ( x e. K , y e. ( P pSyl G ) |-> ran ( z e. y |-> ( ( x .+ z ) .- x ) ) )

  disjoint x y
  disjoint x z
  disjoint .- x
  disjoint y z
  disjoint .- y
  disjoint .- z
  disjoint .(+) x
  disjoint .(+) y
  disjoint .(+) z
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
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
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint .- u
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
  disjoint .(+) u
  disjoint .(+) w
  disjoint H g
  disjoint H x
  disjoint H y
  disjoint g v
  disjoint K g
  disjoint h v
  disjoint K h
  disjoint s v
  disjoint K s
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint g k
  disjoint N g
  disjoint k u
  disjoint k w
  disjoint k z
  disjoint N k
  disjoint N u
  disjoint N w
  disjoint N z
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
  disjoint X u
  disjoint X w
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G g
  disjoint G h
  disjoint k s
  disjoint G k
  disjoint G s
  disjoint G u
  disjoint G w
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint g ph
  disjoint h ph
  disjoint k ph
  disjoint ph s
  disjoint ph u
  disjoint ph w
  disjoint .+ a
  disjoint .+ b
  disjoint .+ c
  disjoint .+ g
  disjoint .+ u
  disjoint .+ v
  disjoint .+ w
  disjoint P a
  disjoint P b
  disjoint P c
  disjoint P g
  disjoint P h
  disjoint P k
  disjoint P s
  disjoint P u
  disjoint P w
  assert |- ( ph -> .(+) e. ( ( G |`s K ) GrpAct ( P pSyl G ) ) )

  proof
    wph
    vx
    vy
    cX
    cP
    cG
    cslw
    co
    #
    vz
    vy
    cv
    #
    vx
    cv
    #
    vz
    cv
    #
    c.pl
    co
    #
    @2
    c.mi
    co
    #
    cmpt
    #
    crn
    #
    cmpt2
    #
    cK
    @0
    cxp
    cres
    #
    c.po
    cG
    cK
    cress
    co
    #
    @0
    cga
    co
    #
    wph
    @9
    vx
    vy
    cK
    @0
    @7
    cmpt2
    #
    c.po
    wph
    cK
    cX
    wss
    #
    @0
    @0
    wss
    @9
    @12
    wceq
    wph
    cK
    cG
    csubg
    cfv
    wcel
    #
    @13
    wph
    cK
    @0
    wcel
    @14
    sylow3lem5.k
    cP
    cG
    cK
    slwsubg
    syl
    #
    cX
    cK
    cG
    sylow3.x
    subgss
    syl
    @0
    ssid
    vx
    vy
    cX
    @0
    cK
    @0
    @7
    resmpt2
    sylancl
    sylow3lem5.m
    syl6eqr
    wph
    @8
    cG
    @0
    cga
    co
    wcel
    @14
    @9
    @11
    wcel
    wph
    va
    vb
    vc
    cP
    c.pl
    @8
    cG
    c.mi
    cX
    sylow3.x
    sylow3.g
    sylow3.xf
    sylow3.p
    sylow3lem5.a
    sylow3lem5.d
    vx
    vy
    va
    vb
    cX
    @0
    @7
    vc
    vb
    cv
    #
    va
    cv
    #
    vc
    cv
    #
    c.pl
    co
    #
    @17
    c.mi
    co
    #
    cmpt
    #
    crn
    vc
    @1
    @20
    cmpt
    #
    crn
    @2
    @17
    wceq
    #
    @6
    @22
    @23
    @6
    vc
    @1
    @2
    @18
    c.pl
    co
    #
    @2
    c.mi
    co
    #
    cmpt
    @22
    vz
    vc
    @1
    @5
    @25
    @3
    @18
    wceq
    @4
    @24
    @2
    c.mi
    @3
    @18
    @2
    c.pl
    oveq2
    oveq1d
    cbvmptv
    @23
    vc
    @1
    @25
    @20
    @23
    @24
    @19
    @2
    @17
    c.mi
    @2
    @17
    @18
    c.pl
    oveq1
    @23
    id
    oveq12d
    mpteq2dv
    syl5eq
    rneqd
    @1
    @16
    wceq
    @22
    @21
    vc
    @1
    @16
    @20
    mpteq1
    rneqd
    cbvmpt2v
    sylow3lem1
    @15
    @8
    cK
    cG
    @10
    @0
    @10
    eqid
    gasubg
    syl2anc
    eqeltrrd
end
