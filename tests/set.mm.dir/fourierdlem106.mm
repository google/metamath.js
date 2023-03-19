include "cn.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "cpi.mm"
include "cneg.mm"
include "wceq.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cfzo.mm"
include "wral.mm"
include "cr.mm"
include "cfz.mm"
include "cmap.mm"
include "crab.mm"
include "cmpt.mm"
include "cmin.mm"
include "cdiv.mm"
include "cfl.mm"
include "cmul.mm"
include "ctp.mm"
include "cicc.mm"
include "cdm.mm"
include "cdif.mm"
include "cun.mm"
include "chash.mm"
include "wiso.mm"
include "cio.mm"
include "eqid.mm"
include "id.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "isoeq1.mm"
include "cbviotav.mm"
include "fourierdlem102.mm"

theorem fourierdlem106
  let wph: wff ph
  let vx: setvar x
  let cT: class T
  let cF: class F
  let cG: class G
  let cX: class X
  let vk: setvar k
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  let vw: setvar w
  let vy: setvar y
  assume fourierdlem106.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem106.t: |- T = ( 2 x. _pi )
  assume fourierdlem106.per: |- ( ( ph /\ x e. RR ) -> ( F ` ( x + T ) ) = ( F ` x ) )
  assume fourierdlem106.g: |- G = ( ( RR _D F ) |` ( -u _pi (,) _pi ) )
  assume fourierdlem106.dmdv: |- ( ph -> ( ( -u _pi (,) _pi ) \ dom G ) e. Fin )
  assume fourierdlem106.dvcn: |- ( ph -> G e. ( dom G -cn-> CC ) )
  assume fourierdlem106.rlim: |- ( ( ph /\ x e. ( ( -u _pi [,) _pi ) \ dom G ) ) -> ( ( G |` ( x (,) +oo ) ) limCC x ) =/= (/) )
  assume fourierdlem106.llim: |- ( ( ph /\ x e. ( ( -u _pi (,] _pi ) \ dom G ) ) -> ( ( G |` ( -oo (,) x ) ) limCC x ) =/= (/) )
  assume fourierdlem106.x: |- ( ph -> X e. RR )

  disjoint F x
  disjoint G x
  disjoint T x
  disjoint X x
  disjoint ph x
  disjoint F k
  disjoint F z
  disjoint k x
  disjoint k z
  disjoint x z
  disjoint G f
  disjoint G g
  disjoint f g
  disjoint G k
  disjoint G w
  disjoint G z
  disjoint g k
  disjoint g w
  disjoint g z
  disjoint k w
  disjoint w z
  disjoint g x
  disjoint T f
  disjoint T g
  disjoint T y
  disjoint f y
  disjoint g y
  disjoint T k
  disjoint T w
  disjoint T z
  disjoint k y
  disjoint w y
  disjoint y z
  disjoint x y
  disjoint X f
  disjoint X g
  disjoint X k
  disjoint X w
  disjoint X z
  disjoint f ph
  disjoint k ph
  disjoint ph z
  disjoint k x
  assert |- ( ph -> ( ( ( F |` ( -oo (,) X ) ) limCC X ) =/= (/) /\ ( ( F |` ( X (,) +oo ) ) limCC X ) =/= (/) ) )

  proof
    wph
    vx
    vk
    cn
    cc0
    vw
    cv
    #
    cfv
    cpi
    cneg
    #
    wceq
    vk
    cv
    #
    @0
    cfv
    cpi
    wceq
    wa
    vz
    cv
    #
    @0
    cfv
    @3
    c1
    caddc
    co
    @0
    cfv
    clt
    wbr
    vz
    cc0
    @2
    cfzo
    co
    wral
    wa
    vw
    cr
    cc0
    @2
    cfz
    co
    cmap
    co
    crab
    cmpt
    #
    cc0
    @1
    cpi
    cX
    vy
    cr
    vy
    cv
    #
    cpi
    @5
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cT
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    #
    cfv
    ctp
    @1
    cpi
    cicc
    co
    cG
    cdm
    cdif
    cun
    #
    chash
    cfv
    c1
    cmin
    co
    #
    cfz
    co
    #
    @12
    clt
    clt
    vg
    cv
    #
    wiso
    #
    vg
    cio
    cT
    vf
    vz
    vk
    @11
    cF
    cG
    @12
    @13
    cX
    vw
    fourierdlem106.f
    fourierdlem106.t
    fourierdlem106.per
    fourierdlem106.g
    fourierdlem106.dmdv
    fourierdlem106.dvcn
    fourierdlem106.rlim
    fourierdlem106.llim
    fourierdlem106.x
    @4
    eqid
    vy
    vx
    cr
    @10
    vx
    cv
    #
    cpi
    @17
    cmin
    co
    #
    cT
    cdiv
    co
    #
    cfl
    cfv
    #
    cT
    cmul
    co
    #
    caddc
    co
    @5
    @17
    wceq
    #
    @5
    @17
    @9
    @21
    caddc
    @22
    id
    @22
    @8
    @20
    cT
    cmul
    @22
    @7
    @19
    cfl
    @22
    @6
    @18
    cT
    cdiv
    @5
    @17
    cpi
    cmin
    oveq2
    oveq1d
    fveq2d
    oveq1d
    oveq12d
    cbvmptv
    @12
    eqid
    @13
    eqid
    @16
    @14
    @12
    clt
    clt
    vf
    cv
    #
    wiso
    vg
    vf
    @14
    @12
    clt
    clt
    @23
    @15
    isoeq1
    cbviotav
    fourierdlem102
end
