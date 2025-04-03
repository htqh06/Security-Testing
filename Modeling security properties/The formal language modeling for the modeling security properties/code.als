// Alloy 模型签名定义
sig User {}  // 用户实体

sig Data { 
  owner: one User,               // 数据拥有者
  allowedReaders: set User,      // 被授权可读取该数据的用户集合
  allowedWriters: set User       // 被授权可修改该数据的用户集合
}

// 确保每条数据的拥有者自动具有读取/写入权限
fact OwnerHasAccess {
  all d: Data { 
    d.owner in d.allowedReaders 
    && d.owner in d.allowedWriters 
  }
}

abstract sig Action { 
  user: one User                 // 执行该操作的用户 
}

sig LoginAction extends Action {}              // 登录操作
sig ReadAction extends Action { data: one Data }   // 读取数据操作
sig WriteAction extends Action { data: one Data }  // 写入数据操作

sig LogEntry { 
  action: one Action,            // 被记录的操作
  user: one User                 // 日志中记录的用户
}

// 模型约束：安全属性
// 1. 机密性: 只有被授权的用户才能读取数据
fact Confidentiality {
  all r: ReadAction | 
    r.user in r.data.allowedReaders
}

// 2. 完整性: 只有被授权的用户才能写入/修改数据
fact Integrity {
  all w: WriteAction | 
    w.user in w.data.allowedWriters
}

// 3. 真实性: 除登录操作外，其他操作的执行用户必须已登录过（有对应的LoginAction）
fact Authenticity {
  all a: Action - LoginAction |  // 对于所有非登录的操作
    some l: LoginAction | l.user = a.user
    // 存在某个登录操作 l，其 user 与该操作执行者相同
}

// 4. 问责性: 日志条目中的用户应与实际执行操作的用户一致
fact Accountability {
  all le: LogEntry | 
    le.user = le.action.user
}

// 5. 不可抵赖性: 系统中的每个操作都应有至少一条日志记录
fact NonRepudiation {
  all a: Action | 
    some le: LogEntry | le.action = a
    // 每个操作 a 存在某日志条目 le 记录了该操作 
}

// 断言：安全属性验证
assert NoUnauthorizedRead {
  // 无未授权的数据读取行为发生
  no r: ReadAction | r.user not in r.data.allowedReaders
}
assert NoUnauthorizedWrite {
  // 无未授权的数据写入行为发生
  no w: WriteAction | w.user not in w.data.allowedWriters
}
assert AllActionsAuthenticated {
  // 所有非登录操作均有对应的登录
  no a: Action - LoginAction | 
    no (LoginAction & (user = a.user))
    // 不存在这样一个非登录操作 a：找不到任何 LoginAction 属于该用户
}
assert LogRecordsAccurate {
  // 所有日志准确记录了执行人
  no le: LogEntry | le.user != le.action.user
}
assert AllActionsLogged {
  // 所有操作均已记录日志
  no a: Action | no (LogEntry & (action = a))
}
